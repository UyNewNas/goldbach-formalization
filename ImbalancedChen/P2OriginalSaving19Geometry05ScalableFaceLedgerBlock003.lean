import ImbalancedChen.P2OriginalSaving19Geometry05ScalableInput

/-! Original face_ledger grouped chunk transitions, including exact compact-input binding.
The original packed input, original parser and original decoder are unchanged.
This is a source-only candidate until normal, kernel and full-owned checks pass. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

namespace FaceLedgerBlock003

noncomputable def fragment0094007Chars : List Char := ['{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}']
noncomputable def fragment0094007Value : SourceJson := .obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '0'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['5'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['1', '0'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['7']), .number (String.ofList ['8'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['7']), .number (String.ofList ['1', '0'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['8']), .number (String.ofList ['1', '0'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '0'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['5']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '0'])], .arr [.number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '0'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['1']))]

theorem value_fragment0094007 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 19) (fragment0094007Chars ++ tail) =
      .ok (fragment0094007Value, tail) := by rfl

noncomputable def fragment0094779Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0094779Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0094779Field000Value00 : SourceJson := .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '2'])]
noncomputable def fragment0094779Acc00100 : List (String × SourceJson) := (fragment0094779Field000Key00, fragment0094779Field000Value00) :: fragment0094779Acc00000
noncomputable def fragment0094779Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0094779_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 20) (SourceJson.white (fragment0094779Field000Chars00 ++ tail)) fragment0094779Acc00000 =
      SourceJson.object (fuel + 19) (SourceJson.white tail) fragment0094779Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0094779_object_field_000"
  err.flush

noncomputable def fragment0094779Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0094779Field001Value00 : SourceJson := .number (String.ofList ['6'])
noncomputable def fragment0094779Acc00200 : List (String × SourceJson) := (fragment0094779Field001Key00, fragment0094779Field001Value00) :: fragment0094779Acc00100
noncomputable def fragment0094779Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '6', ',']

theorem object_fragment0094779_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 19) (SourceJson.white (fragment0094779Field001Chars00 ++ tail)) fragment0094779Acc00100 =
      SourceJson.object (fuel + 18) (SourceJson.white tail) fragment0094779Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0094779_object_field_001"
  err.flush

noncomputable def fragment0094779Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0094779Field002Value00 : SourceJson := .number (String.ofList ['1', '2'])
noncomputable def fragment0094779Acc00300 : List (String × SourceJson) := (fragment0094779Field002Key00, fragment0094779Field002Value00) :: fragment0094779Acc00200
noncomputable def fragment0094779Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '1', '2', ',']

theorem object_fragment0094779_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 18) (SourceJson.white (fragment0094779Field002Chars00 ++ tail)) fragment0094779Acc00200 =
      SourceJson.object (fuel + 17) (SourceJson.white tail) fragment0094779Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0094779_object_field_002"
  err.flush

noncomputable def fragment0094779Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0094779Field003Value00 : SourceJson := .arr [.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '0'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '2'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['7']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '2'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '2'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '2'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['5']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '2'])], .arr [.number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '2'])]]
noncomputable def fragment0094779Acc00400 : List (String × SourceJson) := (fragment0094779Field003Key00, fragment0094779Field003Value00) :: fragment0094779Acc00300
noncomputable def fragment0094779Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0094779_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 17) (SourceJson.white (fragment0094779Field003Chars00 ++ tail)) fragment0094779Acc00300 =
      SourceJson.object (fuel + 16) (SourceJson.white tail) fragment0094779Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0094779_object_field_003"
  err.flush

noncomputable def fragment0094779Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0094779Field004Value00 : SourceJson := .number (String.ofList ['1'])
noncomputable def fragment0094779Acc00500 : List (String × SourceJson) := (fragment0094779Field004Key00, fragment0094779Field004Value00) :: fragment0094779Acc00400
noncomputable def fragment0094779Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0094779_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 16) (SourceJson.white (fragment0094779Field004Chars00 ++ tail)) fragment0094779Acc00400 =
      .ok (.obj (fragment0094779Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0094779_object_field_004"
  err.flush

noncomputable def fragment0094779Chars : List Char := '{' :: (fragment0094779Field000Chars00 ++ fragment0094779Field001Chars00 ++ fragment0094779Field002Chars00 ++ fragment0094779Field003Chars00 ++ fragment0094779Field004Chars00)
noncomputable def fragment0094779Value : SourceJson := .obj (fragment0094779Acc00500.reverse)

theorem value_fragment0094779 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 21) (fragment0094779Chars ++ tail) =
      .ok (fragment0094779Value, tail) := by
  have hinput : fragment0094779Chars ++ tail = '{' :: (fragment0094779Field000Chars00 ++ (fragment0094779Field001Chars00 ++ (fragment0094779Field002Chars00 ++ (fragment0094779Field003Chars00 ++ (fragment0094779Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0094779Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 21) (fragment0094779Chars ++ tail) =
        SourceJson.value (fuel + 21) ('{' :: (fragment0094779Field000Chars00 ++ (fragment0094779Field001Chars00 ++ (fragment0094779Field002Chars00 ++ (fragment0094779Field003Chars00 ++ (fragment0094779Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 21)) hinput
    _ = SourceJson.object (fuel + 20) (SourceJson.white (fragment0094779Field000Chars00 ++ (fragment0094779Field001Chars00 ++ (fragment0094779Field002Chars00 ++ (fragment0094779Field003Chars00 ++ (fragment0094779Field004Chars00 ++ (tail))))))) fragment0094779Acc00000 := by rfl
    _ = SourceJson.object (fuel + 19) (SourceJson.white (fragment0094779Field001Chars00 ++ (fragment0094779Field002Chars00 ++ (fragment0094779Field003Chars00 ++ (fragment0094779Field004Chars00 ++ (tail)))))) fragment0094779Acc00100 := object_fragment0094779_field_000 fuel (fragment0094779Field001Chars00 ++ (fragment0094779Field002Chars00 ++ (fragment0094779Field003Chars00 ++ (fragment0094779Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 18) (SourceJson.white (fragment0094779Field002Chars00 ++ (fragment0094779Field003Chars00 ++ (fragment0094779Field004Chars00 ++ (tail))))) fragment0094779Acc00200 := object_fragment0094779_field_001 fuel (fragment0094779Field002Chars00 ++ (fragment0094779Field003Chars00 ++ (fragment0094779Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 17) (SourceJson.white (fragment0094779Field003Chars00 ++ (fragment0094779Field004Chars00 ++ (tail)))) fragment0094779Acc00300 := object_fragment0094779_field_002 fuel (fragment0094779Field003Chars00 ++ (fragment0094779Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 16) (SourceJson.white (fragment0094779Field004Chars00 ++ (tail))) fragment0094779Acc00400 := object_fragment0094779_field_003 fuel (fragment0094779Field004Chars00 ++ (tail))
    _ = .ok (fragment0094779Value, tail) := object_fragment0094779_field_004 fuel (tail)

noncomputable def fragment0096034Acc00000 : List SourceJson := []

noncomputable def fragment0096034Chunk000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0096034Chunk000Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4'])]) :: ((.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '2'])]) :: (acc))

theorem array_fragment0096034_chunk_000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 22) (SourceJson.white (fragment0096034Chunk000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 20) (SourceJson.white tail) (fragment0096034Chunk000Push00 acc) := by
  rfl

noncomputable def fragment0096034Acc00100 : List SourceJson := fragment0096034Chunk000Push00 fragment0096034Acc00000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0096034_array_chunk_000"
  err.flush

noncomputable def fragment0096034Chunk001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0096034Chunk001Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['7']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '6'])]) :: ((.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '6'])]) :: (acc))

theorem array_fragment0096034_chunk_001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 20) (SourceJson.white (fragment0096034Chunk001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 18) (SourceJson.white tail) (fragment0096034Chunk001Push00 acc) := by
  rfl

noncomputable def fragment0096034Acc00200 : List SourceJson := fragment0096034Chunk001Push00 fragment0096034Acc00100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0096034_array_chunk_001"
  err.flush

noncomputable def fragment0096034Chunk002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0096034Chunk002Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '6'])]) :: ((.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '7']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '6'])]) :: (acc))

theorem array_fragment0096034_chunk_002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 18) (SourceJson.white (fragment0096034Chunk002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 16) (SourceJson.white tail) (fragment0096034Chunk002Push00 acc) := by
  rfl

noncomputable def fragment0096034Acc00300 : List SourceJson := fragment0096034Chunk002Push00 fragment0096034Acc00200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0096034_array_chunk_002"
  err.flush

noncomputable def fragment0096034Chunk003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0096034Chunk003Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '6'])]) :: ((.arr [.number (String.ofList ['1']), .number (String.ofList ['5']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '6'])]) :: (acc))

theorem array_fragment0096034_chunk_003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 16) (SourceJson.white (fragment0096034Chunk003Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 14) (SourceJson.white tail) (fragment0096034Chunk003Push00 acc) := by
  rfl

noncomputable def fragment0096034Acc00400 : List SourceJson := fragment0096034Chunk003Push00 fragment0096034Acc00300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0096034_array_chunk_003"
  err.flush

noncomputable def fragment0096034Chunk004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']']
noncomputable def fragment0096034Chunk004Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1', '5']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '6'])]) :: (acc)

theorem array_fragment0096034_chunk_004 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 14) (SourceJson.white (fragment0096034Chunk004Chars00 ++ tail)) acc =
      .ok (.arr ((fragment0096034Chunk004Push00 acc).reverse), tail) := by
  rfl

noncomputable def fragment0096034Acc00500 : List SourceJson := fragment0096034Chunk004Push00 fragment0096034Acc00400

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0096034_array_chunk_004"
  err.flush

noncomputable def fragment0096034Chars : List Char := '[' :: (fragment0096034Chunk000Chars00 ++ fragment0096034Chunk001Chars00 ++ fragment0096034Chunk002Chars00 ++ fragment0096034Chunk003Chars00 ++ fragment0096034Chunk004Chars00)
noncomputable def fragment0096034Value : SourceJson := .arr (fragment0096034Acc00500.reverse)

theorem value_fragment0096034 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 23) (fragment0096034Chars ++ tail) =
      .ok (fragment0096034Value, tail) := by
  have hinput : fragment0096034Chars ++ tail = '[' :: (fragment0096034Chunk000Chars00 ++ (fragment0096034Chunk001Chars00 ++ (fragment0096034Chunk002Chars00 ++ (fragment0096034Chunk003Chars00 ++ (fragment0096034Chunk004Chars00 ++ (tail)))))) := by
    simp only [fragment0096034Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 23) (fragment0096034Chars ++ tail) =
        SourceJson.value (fuel + 23) ('[' :: (fragment0096034Chunk000Chars00 ++ (fragment0096034Chunk001Chars00 ++ (fragment0096034Chunk002Chars00 ++ (fragment0096034Chunk003Chars00 ++ (fragment0096034Chunk004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 23)) hinput
    _ = SourceJson.array (fuel + 22) (SourceJson.white (fragment0096034Chunk000Chars00 ++ (fragment0096034Chunk001Chars00 ++ (fragment0096034Chunk002Chars00 ++ (fragment0096034Chunk003Chars00 ++ (fragment0096034Chunk004Chars00 ++ (tail))))))) fragment0096034Acc00000 := by rfl
    _ = SourceJson.array (fuel + 20) (SourceJson.white (fragment0096034Chunk001Chars00 ++ (fragment0096034Chunk002Chars00 ++ (fragment0096034Chunk003Chars00 ++ (fragment0096034Chunk004Chars00 ++ (tail)))))) fragment0096034Acc00100 := array_fragment0096034_chunk_000 fuel (fragment0096034Chunk001Chars00 ++ (fragment0096034Chunk002Chars00 ++ (fragment0096034Chunk003Chars00 ++ (fragment0096034Chunk004Chars00 ++ (tail))))) fragment0096034Acc00000
    _ = SourceJson.array (fuel + 18) (SourceJson.white (fragment0096034Chunk002Chars00 ++ (fragment0096034Chunk003Chars00 ++ (fragment0096034Chunk004Chars00 ++ (tail))))) fragment0096034Acc00200 := array_fragment0096034_chunk_001 fuel (fragment0096034Chunk002Chars00 ++ (fragment0096034Chunk003Chars00 ++ (fragment0096034Chunk004Chars00 ++ (tail)))) fragment0096034Acc00100
    _ = SourceJson.array (fuel + 16) (SourceJson.white (fragment0096034Chunk003Chars00 ++ (fragment0096034Chunk004Chars00 ++ (tail)))) fragment0096034Acc00300 := array_fragment0096034_chunk_002 fuel (fragment0096034Chunk003Chars00 ++ (fragment0096034Chunk004Chars00 ++ (tail))) fragment0096034Acc00200
    _ = SourceJson.array (fuel + 14) (SourceJson.white (fragment0096034Chunk004Chars00 ++ (tail))) fragment0096034Acc00400 := array_fragment0096034_chunk_003 fuel (fragment0096034Chunk004Chars00 ++ (tail)) fragment0096034Acc00300
    _ = .ok (fragment0096034Value, tail) := array_fragment0096034_chunk_004 fuel (tail) fragment0096034Acc00400

noncomputable def fragment0095761Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0095761Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0095761Field000Value00 : SourceJson := .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '6'])]
noncomputable def fragment0095761Acc00100 : List (String × SourceJson) := (fragment0095761Field000Key00, fragment0095761Field000Value00) :: fragment0095761Acc00000
noncomputable def fragment0095761Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0095761_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 27) (SourceJson.white (fragment0095761Field000Chars00 ++ tail)) fragment0095761Acc00000 =
      SourceJson.object (fuel + 26) (SourceJson.white tail) fragment0095761Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0095761_object_field_000"
  err.flush

noncomputable def fragment0095761Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0095761Field001Value00 : SourceJson := .number (String.ofList ['7'])
noncomputable def fragment0095761Acc00200 : List (String × SourceJson) := (fragment0095761Field001Key00, fragment0095761Field001Value00) :: fragment0095761Acc00100
noncomputable def fragment0095761Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '7', ',']

theorem object_fragment0095761_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 26) (SourceJson.white (fragment0095761Field001Chars00 ++ tail)) fragment0095761Acc00100 =
      SourceJson.object (fuel + 25) (SourceJson.white tail) fragment0095761Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0095761_object_field_001"
  err.flush

noncomputable def fragment0095761Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0095761Field002Value00 : SourceJson := .number (String.ofList ['2', '6'])
noncomputable def fragment0095761Acc00300 : List (String × SourceJson) := (fragment0095761Field002Key00, fragment0095761Field002Value00) :: fragment0095761Acc00200
noncomputable def fragment0095761Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '2', '6', ',']

theorem object_fragment0095761_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 25) (SourceJson.white (fragment0095761Field002Chars00 ++ tail)) fragment0095761Acc00200 =
      SourceJson.object (fuel + 24) (SourceJson.white tail) fragment0095761Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0095761_object_field_002"
  err.flush

noncomputable def fragment0095761Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0095761Field003Value00 : SourceJson := fragment0096034Value
noncomputable def fragment0095761Acc00400 : List (String × SourceJson) := (fragment0095761Field003Key00, fragment0095761Field003Value00) :: fragment0095761Acc00300
noncomputable def fragment0095761Field003HeaderChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ']
noncomputable def fragment0095761Field003SuffixChars00 : List Char := [',']
noncomputable def fragment0095761Field003Chars00 : List Char := fragment0095761Field003HeaderChars00 ++ fragment0096034Chars ++ fragment0095761Field003SuffixChars00

noncomputable def fragment0095761Field003AfterValue00 (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending => .ok (.obj (((fragment0095761Field003Key00, result.1) :: fragment0095761Acc00300).reverse), ending)
  | ',' :: ending => SourceJson.object fuel (SourceJson.white ending) ((fragment0095761Field003Key00, result.1) :: fragment0095761Acc00300)
  | _ => .error "object separator missing"

theorem object_fragment0095761_field_003_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 24) (SourceJson.white (fragment0095761Field003HeaderChars00 ++ rest)) fragment0095761Acc00300 =
      (SourceJson.value (fuel + 23) rest).bind (fragment0095761Field003AfterValue00 (fuel + 23)) := by rfl

theorem object_fragment0095761_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 24) (SourceJson.white (fragment0095761Field003Chars00 ++ tail)) fragment0095761Acc00300 =
      SourceJson.object (fuel + 23) (SourceJson.white tail) fragment0095761Acc00400 := by
  have hinput : fragment0095761Field003Chars00 ++ tail = fragment0095761Field003HeaderChars00 ++ (fragment0096034Chars ++ (fragment0095761Field003SuffixChars00 ++ tail)) := by
    simp only [fragment0095761Field003Chars00, List.append_assoc]
  calc
    SourceJson.object (fuel + 24) (SourceJson.white (fragment0095761Field003Chars00 ++ tail)) fragment0095761Acc00300 =
        SourceJson.object (fuel + 24)
          (SourceJson.white (fragment0095761Field003HeaderChars00 ++ (fragment0096034Chars ++ (fragment0095761Field003SuffixChars00 ++ tail)))) fragment0095761Acc00300 :=
      congrArg (fun s => SourceJson.object (fuel + 24) (SourceJson.white s) fragment0095761Acc00300) hinput
    _ = (SourceJson.value (fuel + 23) (fragment0096034Chars ++ (fragment0095761Field003SuffixChars00 ++ tail))).bind
        (fragment0095761Field003AfterValue00 (fuel + 23)) := object_fragment0095761_field_003_header fuel (fragment0096034Chars ++ (fragment0095761Field003SuffixChars00 ++ tail))
    _ = (Except.ok (fragment0096034Value, fragment0095761Field003SuffixChars00 ++ tail)).bind (fragment0095761Field003AfterValue00 (fuel + 23)) :=
      congrArg (fun result => result.bind (fragment0095761Field003AfterValue00 (fuel + 23)))
        (value_fragment0096034 (fuel + 0) (fragment0095761Field003SuffixChars00 ++ tail))
    _ = SourceJson.object (fuel + 23) (SourceJson.white tail) fragment0095761Acc00400 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0095761_object_field_003"
  err.flush

noncomputable def fragment0095761Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0095761Field004Value00 : SourceJson := .number (String.ofList ['7'])
noncomputable def fragment0095761Acc00500 : List (String × SourceJson) := (fragment0095761Field004Key00, fragment0095761Field004Value00) :: fragment0095761Acc00400
noncomputable def fragment0095761Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '7', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0095761_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 23) (SourceJson.white (fragment0095761Field004Chars00 ++ tail)) fragment0095761Acc00400 =
      .ok (.obj (fragment0095761Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0095761_object_field_004"
  err.flush

noncomputable def fragment0095761Chars : List Char := '{' :: (fragment0095761Field000Chars00 ++ fragment0095761Field001Chars00 ++ fragment0095761Field002Chars00 ++ fragment0095761Field003Chars00 ++ fragment0095761Field004Chars00)
noncomputable def fragment0095761Value : SourceJson := .obj (fragment0095761Acc00500.reverse)

theorem value_fragment0095761 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 28) (fragment0095761Chars ++ tail) =
      .ok (fragment0095761Value, tail) := by
  have hinput : fragment0095761Chars ++ tail = '{' :: (fragment0095761Field000Chars00 ++ (fragment0095761Field001Chars00 ++ (fragment0095761Field002Chars00 ++ (fragment0095761Field003Chars00 ++ (fragment0095761Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0095761Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 28) (fragment0095761Chars ++ tail) =
        SourceJson.value (fuel + 28) ('{' :: (fragment0095761Field000Chars00 ++ (fragment0095761Field001Chars00 ++ (fragment0095761Field002Chars00 ++ (fragment0095761Field003Chars00 ++ (fragment0095761Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 28)) hinput
    _ = SourceJson.object (fuel + 27) (SourceJson.white (fragment0095761Field000Chars00 ++ (fragment0095761Field001Chars00 ++ (fragment0095761Field002Chars00 ++ (fragment0095761Field003Chars00 ++ (fragment0095761Field004Chars00 ++ (tail))))))) fragment0095761Acc00000 := by rfl
    _ = SourceJson.object (fuel + 26) (SourceJson.white (fragment0095761Field001Chars00 ++ (fragment0095761Field002Chars00 ++ (fragment0095761Field003Chars00 ++ (fragment0095761Field004Chars00 ++ (tail)))))) fragment0095761Acc00100 := object_fragment0095761_field_000 fuel (fragment0095761Field001Chars00 ++ (fragment0095761Field002Chars00 ++ (fragment0095761Field003Chars00 ++ (fragment0095761Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 25) (SourceJson.white (fragment0095761Field002Chars00 ++ (fragment0095761Field003Chars00 ++ (fragment0095761Field004Chars00 ++ (tail))))) fragment0095761Acc00200 := object_fragment0095761_field_001 fuel (fragment0095761Field002Chars00 ++ (fragment0095761Field003Chars00 ++ (fragment0095761Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 24) (SourceJson.white (fragment0095761Field003Chars00 ++ (fragment0095761Field004Chars00 ++ (tail)))) fragment0095761Acc00300 := object_fragment0095761_field_002 fuel (fragment0095761Field003Chars00 ++ (fragment0095761Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 23) (SourceJson.white (fragment0095761Field004Chars00 ++ (tail))) fragment0095761Acc00400 := object_fragment0095761_field_003 fuel (fragment0095761Field004Chars00 ++ (tail))
    _ = .ok (fragment0095761Value, tail) := object_fragment0095761_field_004 fuel (tail)

noncomputable def fragment0097960Acc00000 : List SourceJson := []

noncomputable def fragment0097960Chunk000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0097960Chunk000Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '4'])]) :: ((.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '0'])]) :: (acc))

theorem array_fragment0097960_chunk_000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 19) (SourceJson.white (fragment0097960Chunk000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 17) (SourceJson.white tail) (fragment0097960Chunk000Push00 acc) := by
  rfl

noncomputable def fragment0097960Acc00100 : List SourceJson := fragment0097960Chunk000Push00 fragment0097960Acc00000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0097960_array_chunk_000"
  err.flush

noncomputable def fragment0097960Chunk001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0097960Chunk001Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '7']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4'])]) :: ((.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['7']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3'])]) :: (acc))

theorem array_fragment0097960_chunk_001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 17) (SourceJson.white (fragment0097960Chunk001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 15) (SourceJson.white tail) (fragment0097960Chunk001Push00 acc) := by
  rfl

noncomputable def fragment0097960Acc00200 : List SourceJson := fragment0097960Chunk001Push00 fragment0097960Acc00100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0097960_array_chunk_001"
  err.flush

noncomputable def fragment0097960Chunk002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0097960Chunk002Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1']), .number (String.ofList ['5']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4'])]) :: ((.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4'])]) :: (acc))

theorem array_fragment0097960_chunk_002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 15) (SourceJson.white (fragment0097960Chunk002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 13) (SourceJson.white tail) (fragment0097960Chunk002Push00 acc) := by
  rfl

noncomputable def fragment0097960Acc00300 : List SourceJson := fragment0097960Chunk002Push00 fragment0097960Acc00200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0097960_array_chunk_002"
  err.flush

noncomputable def fragment0097960Chunk003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']']
noncomputable def fragment0097960Chunk003Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1', '5']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4'])]) :: ((.arr [.number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4'])]) :: (acc))

theorem array_fragment0097960_chunk_003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 13) (SourceJson.white (fragment0097960Chunk003Chars00 ++ tail)) acc =
      .ok (.arr ((fragment0097960Chunk003Push00 acc).reverse), tail) := by
  rfl

noncomputable def fragment0097960Acc00400 : List SourceJson := fragment0097960Chunk003Push00 fragment0097960Acc00300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0097960_array_chunk_003"
  err.flush

noncomputable def fragment0097960Chars : List Char := '[' :: (fragment0097960Chunk000Chars00 ++ fragment0097960Chunk001Chars00 ++ fragment0097960Chunk002Chars00 ++ fragment0097960Chunk003Chars00)
noncomputable def fragment0097960Value : SourceJson := .arr (fragment0097960Acc00400.reverse)

theorem value_fragment0097960 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 20) (fragment0097960Chars ++ tail) =
      .ok (fragment0097960Value, tail) := by
  have hinput : fragment0097960Chars ++ tail = '[' :: (fragment0097960Chunk000Chars00 ++ (fragment0097960Chunk001Chars00 ++ (fragment0097960Chunk002Chars00 ++ (fragment0097960Chunk003Chars00 ++ (tail))))) := by
    simp only [fragment0097960Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 20) (fragment0097960Chars ++ tail) =
        SourceJson.value (fuel + 20) ('[' :: (fragment0097960Chunk000Chars00 ++ (fragment0097960Chunk001Chars00 ++ (fragment0097960Chunk002Chars00 ++ (fragment0097960Chunk003Chars00 ++ (tail)))))) :=
      congrArg (SourceJson.value (fuel + 20)) hinput
    _ = SourceJson.array (fuel + 19) (SourceJson.white (fragment0097960Chunk000Chars00 ++ (fragment0097960Chunk001Chars00 ++ (fragment0097960Chunk002Chars00 ++ (fragment0097960Chunk003Chars00 ++ (tail)))))) fragment0097960Acc00000 := by rfl
    _ = SourceJson.array (fuel + 17) (SourceJson.white (fragment0097960Chunk001Chars00 ++ (fragment0097960Chunk002Chars00 ++ (fragment0097960Chunk003Chars00 ++ (tail))))) fragment0097960Acc00100 := array_fragment0097960_chunk_000 fuel (fragment0097960Chunk001Chars00 ++ (fragment0097960Chunk002Chars00 ++ (fragment0097960Chunk003Chars00 ++ (tail)))) fragment0097960Acc00000
    _ = SourceJson.array (fuel + 15) (SourceJson.white (fragment0097960Chunk002Chars00 ++ (fragment0097960Chunk003Chars00 ++ (tail)))) fragment0097960Acc00200 := array_fragment0097960_chunk_001 fuel (fragment0097960Chunk002Chars00 ++ (fragment0097960Chunk003Chars00 ++ (tail))) fragment0097960Acc00100
    _ = SourceJson.array (fuel + 13) (SourceJson.white (fragment0097960Chunk003Chars00 ++ (tail))) fragment0097960Acc00300 := array_fragment0097960_chunk_002 fuel (fragment0097960Chunk003Chars00 ++ (tail)) fragment0097960Acc00200
    _ = .ok (fragment0097960Value, tail) := array_fragment0097960_chunk_003 fuel (tail) fragment0097960Acc00300

noncomputable def fragment0097713Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0097713Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0097713Field000Value00 : SourceJson := .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4'])]
noncomputable def fragment0097713Acc00100 : List (String × SourceJson) := (fragment0097713Field000Key00, fragment0097713Field000Value00) :: fragment0097713Acc00000
noncomputable def fragment0097713Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0097713_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 24) (SourceJson.white (fragment0097713Field000Chars00 ++ tail)) fragment0097713Acc00000 =
      SourceJson.object (fuel + 23) (SourceJson.white tail) fragment0097713Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0097713_object_field_000"
  err.flush

noncomputable def fragment0097713Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0097713Field001Value00 : SourceJson := .number (String.ofList ['6'])
noncomputable def fragment0097713Acc00200 : List (String × SourceJson) := (fragment0097713Field001Key00, fragment0097713Field001Value00) :: fragment0097713Acc00100
noncomputable def fragment0097713Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '6', ',']

theorem object_fragment0097713_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 23) (SourceJson.white (fragment0097713Field001Chars00 ++ tail)) fragment0097713Acc00100 =
      SourceJson.object (fuel + 22) (SourceJson.white tail) fragment0097713Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0097713_object_field_001"
  err.flush

noncomputable def fragment0097713Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0097713Field002Value00 : SourceJson := .number (String.ofList ['2', '4'])
noncomputable def fragment0097713Acc00300 : List (String × SourceJson) := (fragment0097713Field002Key00, fragment0097713Field002Value00) :: fragment0097713Acc00200
noncomputable def fragment0097713Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '2', '4', ',']

theorem object_fragment0097713_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 22) (SourceJson.white (fragment0097713Field002Chars00 ++ tail)) fragment0097713Acc00200 =
      SourceJson.object (fuel + 21) (SourceJson.white tail) fragment0097713Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0097713_object_field_002"
  err.flush

noncomputable def fragment0097713Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0097713Field003Value00 : SourceJson := fragment0097960Value
noncomputable def fragment0097713Acc00400 : List (String × SourceJson) := (fragment0097713Field003Key00, fragment0097713Field003Value00) :: fragment0097713Acc00300
noncomputable def fragment0097713Field003HeaderChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ']
noncomputable def fragment0097713Field003SuffixChars00 : List Char := [',']
noncomputable def fragment0097713Field003Chars00 : List Char := fragment0097713Field003HeaderChars00 ++ fragment0097960Chars ++ fragment0097713Field003SuffixChars00

noncomputable def fragment0097713Field003AfterValue00 (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending => .ok (.obj (((fragment0097713Field003Key00, result.1) :: fragment0097713Acc00300).reverse), ending)
  | ',' :: ending => SourceJson.object fuel (SourceJson.white ending) ((fragment0097713Field003Key00, result.1) :: fragment0097713Acc00300)
  | _ => .error "object separator missing"

theorem object_fragment0097713_field_003_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 21) (SourceJson.white (fragment0097713Field003HeaderChars00 ++ rest)) fragment0097713Acc00300 =
      (SourceJson.value (fuel + 20) rest).bind (fragment0097713Field003AfterValue00 (fuel + 20)) := by rfl

theorem object_fragment0097713_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 21) (SourceJson.white (fragment0097713Field003Chars00 ++ tail)) fragment0097713Acc00300 =
      SourceJson.object (fuel + 20) (SourceJson.white tail) fragment0097713Acc00400 := by
  have hinput : fragment0097713Field003Chars00 ++ tail = fragment0097713Field003HeaderChars00 ++ (fragment0097960Chars ++ (fragment0097713Field003SuffixChars00 ++ tail)) := by
    simp only [fragment0097713Field003Chars00, List.append_assoc]
  calc
    SourceJson.object (fuel + 21) (SourceJson.white (fragment0097713Field003Chars00 ++ tail)) fragment0097713Acc00300 =
        SourceJson.object (fuel + 21)
          (SourceJson.white (fragment0097713Field003HeaderChars00 ++ (fragment0097960Chars ++ (fragment0097713Field003SuffixChars00 ++ tail)))) fragment0097713Acc00300 :=
      congrArg (fun s => SourceJson.object (fuel + 21) (SourceJson.white s) fragment0097713Acc00300) hinput
    _ = (SourceJson.value (fuel + 20) (fragment0097960Chars ++ (fragment0097713Field003SuffixChars00 ++ tail))).bind
        (fragment0097713Field003AfterValue00 (fuel + 20)) := object_fragment0097713_field_003_header fuel (fragment0097960Chars ++ (fragment0097713Field003SuffixChars00 ++ tail))
    _ = (Except.ok (fragment0097960Value, fragment0097713Field003SuffixChars00 ++ tail)).bind (fragment0097713Field003AfterValue00 (fuel + 20)) :=
      congrArg (fun result => result.bind (fragment0097713Field003AfterValue00 (fuel + 20)))
        (value_fragment0097960 (fuel + 0) (fragment0097713Field003SuffixChars00 ++ tail))
    _ = SourceJson.object (fuel + 20) (SourceJson.white tail) fragment0097713Acc00400 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0097713_object_field_003"
  err.flush

noncomputable def fragment0097713Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0097713Field004Value00 : SourceJson := .number (String.ofList ['6'])
noncomputable def fragment0097713Acc00500 : List (String × SourceJson) := (fragment0097713Field004Key00, fragment0097713Field004Value00) :: fragment0097713Acc00400
noncomputable def fragment0097713Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '6', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0097713_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 20) (SourceJson.white (fragment0097713Field004Chars00 ++ tail)) fragment0097713Acc00400 =
      .ok (.obj (fragment0097713Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0097713_object_field_004"
  err.flush

noncomputable def fragment0097713Chars : List Char := '{' :: (fragment0097713Field000Chars00 ++ fragment0097713Field001Chars00 ++ fragment0097713Field002Chars00 ++ fragment0097713Field003Chars00 ++ fragment0097713Field004Chars00)
noncomputable def fragment0097713Value : SourceJson := .obj (fragment0097713Acc00500.reverse)

theorem value_fragment0097713 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 25) (fragment0097713Chars ++ tail) =
      .ok (fragment0097713Value, tail) := by
  have hinput : fragment0097713Chars ++ tail = '{' :: (fragment0097713Field000Chars00 ++ (fragment0097713Field001Chars00 ++ (fragment0097713Field002Chars00 ++ (fragment0097713Field003Chars00 ++ (fragment0097713Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0097713Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 25) (fragment0097713Chars ++ tail) =
        SourceJson.value (fuel + 25) ('{' :: (fragment0097713Field000Chars00 ++ (fragment0097713Field001Chars00 ++ (fragment0097713Field002Chars00 ++ (fragment0097713Field003Chars00 ++ (fragment0097713Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 25)) hinput
    _ = SourceJson.object (fuel + 24) (SourceJson.white (fragment0097713Field000Chars00 ++ (fragment0097713Field001Chars00 ++ (fragment0097713Field002Chars00 ++ (fragment0097713Field003Chars00 ++ (fragment0097713Field004Chars00 ++ (tail))))))) fragment0097713Acc00000 := by rfl
    _ = SourceJson.object (fuel + 23) (SourceJson.white (fragment0097713Field001Chars00 ++ (fragment0097713Field002Chars00 ++ (fragment0097713Field003Chars00 ++ (fragment0097713Field004Chars00 ++ (tail)))))) fragment0097713Acc00100 := object_fragment0097713_field_000 fuel (fragment0097713Field001Chars00 ++ (fragment0097713Field002Chars00 ++ (fragment0097713Field003Chars00 ++ (fragment0097713Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 22) (SourceJson.white (fragment0097713Field002Chars00 ++ (fragment0097713Field003Chars00 ++ (fragment0097713Field004Chars00 ++ (tail))))) fragment0097713Acc00200 := object_fragment0097713_field_001 fuel (fragment0097713Field002Chars00 ++ (fragment0097713Field003Chars00 ++ (fragment0097713Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 21) (SourceJson.white (fragment0097713Field003Chars00 ++ (fragment0097713Field004Chars00 ++ (tail)))) fragment0097713Acc00300 := object_fragment0097713_field_002 fuel (fragment0097713Field003Chars00 ++ (fragment0097713Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 20) (SourceJson.white (fragment0097713Field004Chars00 ++ (tail))) fragment0097713Acc00400 := object_fragment0097713_field_003 fuel (fragment0097713Field004Chars00 ++ (tail))
    _ = .ok (fragment0097713Value, tail) := object_fragment0097713_field_004 fuel (tail)

noncomputable def fragment0100051Acc00000 : List SourceJson := []

noncomputable def fragment0100051Chunk000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0100051Chunk000Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['7']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '1'])]) :: ((.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['7']), .number (String.ofList ['1', '0'])]) :: (acc))

theorem array_fragment0100051_chunk_000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 16) (SourceJson.white (fragment0100051Chunk000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 14) (SourceJson.white tail) (fragment0100051Chunk000Push00 acc) := by
  rfl

noncomputable def fragment0100051Acc00100 : List SourceJson := fragment0100051Chunk000Push00 fragment0100051Acc00000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0100051_array_chunk_000"
  err.flush

noncomputable def fragment0100051Chunk001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0100051Chunk001Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['7']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3'])]) :: ((.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '7']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3'])]) :: (acc))

theorem array_fragment0100051_chunk_001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 14) (SourceJson.white (fragment0100051Chunk001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 12) (SourceJson.white tail) (fragment0100051Chunk001Push00 acc) := by
  rfl

noncomputable def fragment0100051Acc00200 : List SourceJson := fragment0100051Chunk001Push00 fragment0100051Acc00100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0100051_array_chunk_001"
  err.flush

noncomputable def fragment0100051Chunk002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0100051Chunk002Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['7']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3'])]) :: ((.arr [.number (String.ofList ['1']), .number (String.ofList ['5']), .number (String.ofList ['7']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '3'])]) :: (acc))

theorem array_fragment0100051_chunk_002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 12) (SourceJson.white (fragment0100051Chunk002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 10) (SourceJson.white tail) (fragment0100051Chunk002Push00 acc) := by
  rfl

noncomputable def fragment0100051Acc00300 : List SourceJson := fragment0100051Chunk002Push00 fragment0100051Acc00200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0100051_array_chunk_002"
  err.flush

noncomputable def fragment0100051Chunk003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']']
noncomputable def fragment0100051Chunk003Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1', '5']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3'])]) :: (acc)

theorem array_fragment0100051_chunk_003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 10) (SourceJson.white (fragment0100051Chunk003Chars00 ++ tail)) acc =
      .ok (.arr ((fragment0100051Chunk003Push00 acc).reverse), tail) := by
  rfl

noncomputable def fragment0100051Acc00400 : List SourceJson := fragment0100051Chunk003Push00 fragment0100051Acc00300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0100051_array_chunk_003"
  err.flush

noncomputable def fragment0100051Chars : List Char := '[' :: (fragment0100051Chunk000Chars00 ++ fragment0100051Chunk001Chars00 ++ fragment0100051Chunk002Chars00 ++ fragment0100051Chunk003Chars00)
noncomputable def fragment0100051Value : SourceJson := .arr (fragment0100051Acc00400.reverse)

theorem value_fragment0100051 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 17) (fragment0100051Chars ++ tail) =
      .ok (fragment0100051Value, tail) := by
  have hinput : fragment0100051Chars ++ tail = '[' :: (fragment0100051Chunk000Chars00 ++ (fragment0100051Chunk001Chars00 ++ (fragment0100051Chunk002Chars00 ++ (fragment0100051Chunk003Chars00 ++ (tail))))) := by
    simp only [fragment0100051Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 17) (fragment0100051Chars ++ tail) =
        SourceJson.value (fuel + 17) ('[' :: (fragment0100051Chunk000Chars00 ++ (fragment0100051Chunk001Chars00 ++ (fragment0100051Chunk002Chars00 ++ (fragment0100051Chunk003Chars00 ++ (tail)))))) :=
      congrArg (SourceJson.value (fuel + 17)) hinput
    _ = SourceJson.array (fuel + 16) (SourceJson.white (fragment0100051Chunk000Chars00 ++ (fragment0100051Chunk001Chars00 ++ (fragment0100051Chunk002Chars00 ++ (fragment0100051Chunk003Chars00 ++ (tail)))))) fragment0100051Acc00000 := by rfl
    _ = SourceJson.array (fuel + 14) (SourceJson.white (fragment0100051Chunk001Chars00 ++ (fragment0100051Chunk002Chars00 ++ (fragment0100051Chunk003Chars00 ++ (tail))))) fragment0100051Acc00100 := array_fragment0100051_chunk_000 fuel (fragment0100051Chunk001Chars00 ++ (fragment0100051Chunk002Chars00 ++ (fragment0100051Chunk003Chars00 ++ (tail)))) fragment0100051Acc00000
    _ = SourceJson.array (fuel + 12) (SourceJson.white (fragment0100051Chunk002Chars00 ++ (fragment0100051Chunk003Chars00 ++ (tail)))) fragment0100051Acc00200 := array_fragment0100051_chunk_001 fuel (fragment0100051Chunk002Chars00 ++ (fragment0100051Chunk003Chars00 ++ (tail))) fragment0100051Acc00100
    _ = SourceJson.array (fuel + 10) (SourceJson.white (fragment0100051Chunk003Chars00 ++ (tail))) fragment0100051Acc00300 := array_fragment0100051_chunk_002 fuel (fragment0100051Chunk003Chars00 ++ (tail)) fragment0100051Acc00200
    _ = .ok (fragment0100051Value, tail) := array_fragment0100051_chunk_003 fuel (tail) fragment0100051Acc00300

noncomputable def fragment0099829Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0099829Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0099829Field000Value00 : SourceJson := .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['7']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3'])]
noncomputable def fragment0099829Acc00100 : List (String × SourceJson) := (fragment0099829Field000Key00, fragment0099829Field000Value00) :: fragment0099829Acc00000
noncomputable def fragment0099829Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0099829_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 21) (SourceJson.white (fragment0099829Field000Chars00 ++ tail)) fragment0099829Acc00000 =
      SourceJson.object (fuel + 20) (SourceJson.white tail) fragment0099829Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0099829_object_field_000"
  err.flush

noncomputable def fragment0099829Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0099829Field001Value00 : SourceJson := .number (String.ofList ['5'])
noncomputable def fragment0099829Acc00200 : List (String × SourceJson) := (fragment0099829Field001Key00, fragment0099829Field001Value00) :: fragment0099829Acc00100
noncomputable def fragment0099829Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '5', ',']

theorem object_fragment0099829_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 20) (SourceJson.white (fragment0099829Field001Chars00 ++ tail)) fragment0099829Acc00100 =
      SourceJson.object (fuel + 19) (SourceJson.white tail) fragment0099829Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0099829_object_field_001"
  err.flush

noncomputable def fragment0099829Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0099829Field002Value00 : SourceJson := .number (String.ofList ['2', '3'])
noncomputable def fragment0099829Acc00300 : List (String × SourceJson) := (fragment0099829Field002Key00, fragment0099829Field002Value00) :: fragment0099829Acc00200
noncomputable def fragment0099829Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '2', '3', ',']

theorem object_fragment0099829_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 19) (SourceJson.white (fragment0099829Field002Chars00 ++ tail)) fragment0099829Acc00200 =
      SourceJson.object (fuel + 18) (SourceJson.white tail) fragment0099829Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0099829_object_field_002"
  err.flush

noncomputable def fragment0099829Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0099829Field003Value00 : SourceJson := fragment0100051Value
noncomputable def fragment0099829Acc00400 : List (String × SourceJson) := (fragment0099829Field003Key00, fragment0099829Field003Value00) :: fragment0099829Acc00300
noncomputable def fragment0099829Field003HeaderChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ']
noncomputable def fragment0099829Field003SuffixChars00 : List Char := [',']
noncomputable def fragment0099829Field003Chars00 : List Char := fragment0099829Field003HeaderChars00 ++ fragment0100051Chars ++ fragment0099829Field003SuffixChars00

noncomputable def fragment0099829Field003AfterValue00 (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending => .ok (.obj (((fragment0099829Field003Key00, result.1) :: fragment0099829Acc00300).reverse), ending)
  | ',' :: ending => SourceJson.object fuel (SourceJson.white ending) ((fragment0099829Field003Key00, result.1) :: fragment0099829Acc00300)
  | _ => .error "object separator missing"

theorem object_fragment0099829_field_003_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 18) (SourceJson.white (fragment0099829Field003HeaderChars00 ++ rest)) fragment0099829Acc00300 =
      (SourceJson.value (fuel + 17) rest).bind (fragment0099829Field003AfterValue00 (fuel + 17)) := by rfl

theorem object_fragment0099829_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 18) (SourceJson.white (fragment0099829Field003Chars00 ++ tail)) fragment0099829Acc00300 =
      SourceJson.object (fuel + 17) (SourceJson.white tail) fragment0099829Acc00400 := by
  have hinput : fragment0099829Field003Chars00 ++ tail = fragment0099829Field003HeaderChars00 ++ (fragment0100051Chars ++ (fragment0099829Field003SuffixChars00 ++ tail)) := by
    simp only [fragment0099829Field003Chars00, List.append_assoc]
  calc
    SourceJson.object (fuel + 18) (SourceJson.white (fragment0099829Field003Chars00 ++ tail)) fragment0099829Acc00300 =
        SourceJson.object (fuel + 18)
          (SourceJson.white (fragment0099829Field003HeaderChars00 ++ (fragment0100051Chars ++ (fragment0099829Field003SuffixChars00 ++ tail)))) fragment0099829Acc00300 :=
      congrArg (fun s => SourceJson.object (fuel + 18) (SourceJson.white s) fragment0099829Acc00300) hinput
    _ = (SourceJson.value (fuel + 17) (fragment0100051Chars ++ (fragment0099829Field003SuffixChars00 ++ tail))).bind
        (fragment0099829Field003AfterValue00 (fuel + 17)) := object_fragment0099829_field_003_header fuel (fragment0100051Chars ++ (fragment0099829Field003SuffixChars00 ++ tail))
    _ = (Except.ok (fragment0100051Value, fragment0099829Field003SuffixChars00 ++ tail)).bind (fragment0099829Field003AfterValue00 (fuel + 17)) :=
      congrArg (fun result => result.bind (fragment0099829Field003AfterValue00 (fuel + 17)))
        (value_fragment0100051 (fuel + 0) (fragment0099829Field003SuffixChars00 ++ tail))
    _ = SourceJson.object (fuel + 17) (SourceJson.white tail) fragment0099829Acc00400 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0099829_object_field_003"
  err.flush

noncomputable def fragment0099829Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0099829Field004Value00 : SourceJson := .number (String.ofList ['5'])
noncomputable def fragment0099829Acc00500 : List (String × SourceJson) := (fragment0099829Field004Key00, fragment0099829Field004Value00) :: fragment0099829Acc00400
noncomputable def fragment0099829Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '5', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0099829_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 17) (SourceJson.white (fragment0099829Field004Chars00 ++ tail)) fragment0099829Acc00400 =
      .ok (.obj (fragment0099829Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0099829_object_field_004"
  err.flush

noncomputable def fragment0099829Chars : List Char := '{' :: (fragment0099829Field000Chars00 ++ fragment0099829Field001Chars00 ++ fragment0099829Field002Chars00 ++ fragment0099829Field003Chars00 ++ fragment0099829Field004Chars00)
noncomputable def fragment0099829Value : SourceJson := .obj (fragment0099829Acc00500.reverse)

theorem value_fragment0099829 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 22) (fragment0099829Chars ++ tail) =
      .ok (fragment0099829Value, tail) := by
  have hinput : fragment0099829Chars ++ tail = '{' :: (fragment0099829Field000Chars00 ++ (fragment0099829Field001Chars00 ++ (fragment0099829Field002Chars00 ++ (fragment0099829Field003Chars00 ++ (fragment0099829Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0099829Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 22) (fragment0099829Chars ++ tail) =
        SourceJson.value (fuel + 22) ('{' :: (fragment0099829Field000Chars00 ++ (fragment0099829Field001Chars00 ++ (fragment0099829Field002Chars00 ++ (fragment0099829Field003Chars00 ++ (fragment0099829Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 22)) hinput
    _ = SourceJson.object (fuel + 21) (SourceJson.white (fragment0099829Field000Chars00 ++ (fragment0099829Field001Chars00 ++ (fragment0099829Field002Chars00 ++ (fragment0099829Field003Chars00 ++ (fragment0099829Field004Chars00 ++ (tail))))))) fragment0099829Acc00000 := by rfl
    _ = SourceJson.object (fuel + 20) (SourceJson.white (fragment0099829Field001Chars00 ++ (fragment0099829Field002Chars00 ++ (fragment0099829Field003Chars00 ++ (fragment0099829Field004Chars00 ++ (tail)))))) fragment0099829Acc00100 := object_fragment0099829_field_000 fuel (fragment0099829Field001Chars00 ++ (fragment0099829Field002Chars00 ++ (fragment0099829Field003Chars00 ++ (fragment0099829Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 19) (SourceJson.white (fragment0099829Field002Chars00 ++ (fragment0099829Field003Chars00 ++ (fragment0099829Field004Chars00 ++ (tail))))) fragment0099829Acc00200 := object_fragment0099829_field_001 fuel (fragment0099829Field002Chars00 ++ (fragment0099829Field003Chars00 ++ (fragment0099829Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 18) (SourceJson.white (fragment0099829Field003Chars00 ++ (fragment0099829Field004Chars00 ++ (tail)))) fragment0099829Acc00300 := object_fragment0099829_field_002 fuel (fragment0099829Field003Chars00 ++ (fragment0099829Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 17) (SourceJson.white (fragment0099829Field004Chars00 ++ (tail))) fragment0099829Acc00400 := object_fragment0099829_field_003 fuel (fragment0099829Field004Chars00 ++ (tail))
    _ = .ok (fragment0099829Value, tail) := object_fragment0099829_field_004 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0024_before_reader"
  err.flush

noncomputable def chunk0024Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0024Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['7'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['3'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['7'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['7'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['5']), .number (String.ofList ['7'])], .arr [.number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['7'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['1']))]) :: (acc)

theorem array_chunk0024 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 33) (SourceJson.white (chunk0024Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 32) (SourceJson.white tail) (chunk0024Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0024_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0025_before_reader"
  err.flush

noncomputable def chunk0025Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0025Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['7']), .number (String.ofList ['8'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['4'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['8'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['7'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['8'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['7']), .number (String.ofList ['8'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['5']), .number (String.ofList ['7']), .number (String.ofList ['8'])], .arr [.number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['7']), .number (String.ofList ['8'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['1']))]) :: (acc)

theorem array_chunk0025 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 32) (SourceJson.white (chunk0025Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 31) (SourceJson.white tail) (chunk0025Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0025_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0026_before_reader"
  err.flush

noncomputable def chunk0026Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0026Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '0'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['5'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['1', '0'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['7']), .number (String.ofList ['8'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['7']), .number (String.ofList ['1', '0'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['8']), .number (String.ofList ['1', '0'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '0'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['5']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '0'])], .arr [.number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '0'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['1']))]) :: (acc)

theorem array_chunk0026 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 31) (SourceJson.white (chunk0026Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 30) (SourceJson.white tail) (chunk0026Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0026_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0027_before_reader"
  err.flush

noncomputable def chunk0027LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0027SuffixChars00 : List Char := [',']
noncomputable def chunk0027Chars00 : List Char := chunk0027LeadChars00 ++ fragment0094779Chars ++ chunk0027SuffixChars00
noncomputable def chunk0027Push00 (acc : List SourceJson) : List SourceJson := fragment0094779Value :: acc

noncomputable def chunk0027AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0027_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 30)
      (SourceJson.white (chunk0027LeadChars00 ++ (fragment0094779Chars ++ rest))) acc =
      (SourceJson.value (fuel + 29) (fragment0094779Chars ++ rest)).bind
        (chunk0027AfterValue00 (fuel + 29) acc) := by rfl

theorem array_chunk0027 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 30) (SourceJson.white (chunk0027Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 29) (SourceJson.white tail) (chunk0027Push00 acc) := by
  have hinput : chunk0027Chars00 ++ tail = chunk0027LeadChars00 ++ (fragment0094779Chars ++ (chunk0027SuffixChars00 ++ tail)) := by
    simp only [chunk0027Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 30) (SourceJson.white (chunk0027Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 30)
          (SourceJson.white (chunk0027LeadChars00 ++ (fragment0094779Chars ++ (chunk0027SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 30) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 29) (fragment0094779Chars ++ (chunk0027SuffixChars00 ++ tail))).bind
        (chunk0027AfterValue00 (fuel + 29) acc) := array_chunk0027_head fuel (chunk0027SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0094779Value, chunk0027SuffixChars00 ++ tail)).bind
        (chunk0027AfterValue00 (fuel + 29) acc) :=
      congrArg (fun result => result.bind (chunk0027AfterValue00 (fuel + 29) acc))
        (value_fragment0094779 (fuel + 8) (chunk0027SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 29) (SourceJson.white tail) (chunk0027Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0027_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0028_before_reader"
  err.flush

noncomputable def chunk0028LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0028SuffixChars00 : List Char := [',']
noncomputable def chunk0028Chars00 : List Char := chunk0028LeadChars00 ++ fragment0095761Chars ++ chunk0028SuffixChars00
noncomputable def chunk0028Push00 (acc : List SourceJson) : List SourceJson := fragment0095761Value :: acc

noncomputable def chunk0028AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0028_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 29)
      (SourceJson.white (chunk0028LeadChars00 ++ (fragment0095761Chars ++ rest))) acc =
      (SourceJson.value (fuel + 28) (fragment0095761Chars ++ rest)).bind
        (chunk0028AfterValue00 (fuel + 28) acc) := by rfl

theorem array_chunk0028 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 29) (SourceJson.white (chunk0028Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 28) (SourceJson.white tail) (chunk0028Push00 acc) := by
  have hinput : chunk0028Chars00 ++ tail = chunk0028LeadChars00 ++ (fragment0095761Chars ++ (chunk0028SuffixChars00 ++ tail)) := by
    simp only [chunk0028Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 29) (SourceJson.white (chunk0028Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 29)
          (SourceJson.white (chunk0028LeadChars00 ++ (fragment0095761Chars ++ (chunk0028SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 29) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 28) (fragment0095761Chars ++ (chunk0028SuffixChars00 ++ tail))).bind
        (chunk0028AfterValue00 (fuel + 28) acc) := array_chunk0028_head fuel (chunk0028SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0095761Value, chunk0028SuffixChars00 ++ tail)).bind
        (chunk0028AfterValue00 (fuel + 28) acc) :=
      congrArg (fun result => result.bind (chunk0028AfterValue00 (fuel + 28) acc))
        (value_fragment0095761 (fuel + 0) (chunk0028SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 28) (SourceJson.white tail) (chunk0028Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0028_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0029_before_reader"
  err.flush

noncomputable def chunk0029LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0029SuffixChars00 : List Char := [',']
noncomputable def chunk0029Chars00 : List Char := chunk0029LeadChars00 ++ fragment0097713Chars ++ chunk0029SuffixChars00
noncomputable def chunk0029Push00 (acc : List SourceJson) : List SourceJson := fragment0097713Value :: acc

noncomputable def chunk0029AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0029_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 28)
      (SourceJson.white (chunk0029LeadChars00 ++ (fragment0097713Chars ++ rest))) acc =
      (SourceJson.value (fuel + 27) (fragment0097713Chars ++ rest)).bind
        (chunk0029AfterValue00 (fuel + 27) acc) := by rfl

theorem array_chunk0029 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 28) (SourceJson.white (chunk0029Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 27) (SourceJson.white tail) (chunk0029Push00 acc) := by
  have hinput : chunk0029Chars00 ++ tail = chunk0029LeadChars00 ++ (fragment0097713Chars ++ (chunk0029SuffixChars00 ++ tail)) := by
    simp only [chunk0029Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 28) (SourceJson.white (chunk0029Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 28)
          (SourceJson.white (chunk0029LeadChars00 ++ (fragment0097713Chars ++ (chunk0029SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 28) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 27) (fragment0097713Chars ++ (chunk0029SuffixChars00 ++ tail))).bind
        (chunk0029AfterValue00 (fuel + 27) acc) := array_chunk0029_head fuel (chunk0029SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0097713Value, chunk0029SuffixChars00 ++ tail)).bind
        (chunk0029AfterValue00 (fuel + 27) acc) :=
      congrArg (fun result => result.bind (chunk0029AfterValue00 (fuel + 27) acc))
        (value_fragment0097713 (fuel + 2) (chunk0029SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 27) (SourceJson.white tail) (chunk0029Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0029_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0030_before_reader"
  err.flush

noncomputable def chunk0030Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0030Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['7']), .number (String.ofList ['1', '0'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['4'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['1', '0'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['7'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['1', '0'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['7']), .number (String.ofList ['1', '0'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['5']), .number (String.ofList ['7']), .number (String.ofList ['1', '0'])], .arr [.number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['7']), .number (String.ofList ['1', '0'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['1']))]) :: (acc)

theorem array_chunk0030 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 27) (SourceJson.white (chunk0030Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 26) (SourceJson.white tail) (chunk0030Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0030_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0031_before_reader"
  err.flush

noncomputable def chunk0031LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0031SuffixChars00 : List Char := [',']
noncomputable def chunk0031Chars00 : List Char := chunk0031LeadChars00 ++ fragment0099829Chars ++ chunk0031SuffixChars00
noncomputable def chunk0031Push00 (acc : List SourceJson) : List SourceJson := fragment0099829Value :: acc

noncomputable def chunk0031AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0031_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 26)
      (SourceJson.white (chunk0031LeadChars00 ++ (fragment0099829Chars ++ rest))) acc =
      (SourceJson.value (fuel + 25) (fragment0099829Chars ++ rest)).bind
        (chunk0031AfterValue00 (fuel + 25) acc) := by rfl

theorem array_chunk0031 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 26) (SourceJson.white (chunk0031Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 25) (SourceJson.white tail) (chunk0031Push00 acc) := by
  have hinput : chunk0031Chars00 ++ tail = chunk0031LeadChars00 ++ (fragment0099829Chars ++ (chunk0031SuffixChars00 ++ tail)) := by
    simp only [chunk0031Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 26) (SourceJson.white (chunk0031Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 26)
          (SourceJson.white (chunk0031LeadChars00 ++ (fragment0099829Chars ++ (chunk0031SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 26) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 25) (fragment0099829Chars ++ (chunk0031SuffixChars00 ++ tail))).bind
        (chunk0031AfterValue00 (fuel + 25) acc) := array_chunk0031_head fuel (chunk0031SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0099829Value, chunk0031SuffixChars00 ++ tail)).bind
        (chunk0031AfterValue00 (fuel + 25) acc) :=
      congrArg (fun result => result.bind (chunk0031AfterValue00 (fuel + 25) acc))
        (value_fragment0099829 (fuel + 3) (chunk0031SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 25) (SourceJson.white tail) (chunk0031Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0031_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0024Chars00 ++ chunk0025Chars00 ++ chunk0026Chars00 ++ chunk0027Chars00 ++ chunk0028Chars00 ++ chunk0029Chars00 ++ chunk0030Chars00 ++ chunk0031Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0031Push00 (chunk0030Push00 (chunk0029Push00 (chunk0028Push00 (chunk0027Push00 (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc))))))))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 33) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 25) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0024Chars00 ++ (chunk0025Chars00 ++ (chunk0026Chars00 ++ (chunk0027Chars00 ++ (chunk0028Chars00 ++ (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail)))))))) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 33) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 33) (SourceJson.white (chunk0024Chars00 ++ (chunk0025Chars00 ++ (chunk0026Chars00 ++ (chunk0027Chars00 ++ (chunk0028Chars00 ++ (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail)))))))))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 33) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 32) (SourceJson.white (chunk0025Chars00 ++ (chunk0026Chars00 ++ (chunk0027Chars00 ++ (chunk0028Chars00 ++ (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail))))))))) (chunk0024Push00 (acc)) := array_chunk0024 fuel (chunk0025Chars00 ++ (chunk0026Chars00 ++ (chunk0027Chars00 ++ (chunk0028Chars00 ++ (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail)))))))) (acc)
    _ = SourceJson.array (fuel + 31) (SourceJson.white (chunk0026Chars00 ++ (chunk0027Chars00 ++ (chunk0028Chars00 ++ (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail)))))))) (chunk0025Push00 (chunk0024Push00 (acc))) := array_chunk0025 fuel (chunk0026Chars00 ++ (chunk0027Chars00 ++ (chunk0028Chars00 ++ (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail))))))) (chunk0024Push00 (acc))
    _ = SourceJson.array (fuel + 30) (SourceJson.white (chunk0027Chars00 ++ (chunk0028Chars00 ++ (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail))))))) (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc)))) := array_chunk0026 fuel (chunk0027Chars00 ++ (chunk0028Chars00 ++ (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail)))))) (chunk0025Push00 (chunk0024Push00 (acc)))
    _ = SourceJson.array (fuel + 29) (SourceJson.white (chunk0028Chars00 ++ (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail)))))) (chunk0027Push00 (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc))))) := array_chunk0027 fuel (chunk0028Chars00 ++ (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail))))) (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc))))
    _ = SourceJson.array (fuel + 28) (SourceJson.white (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail))))) (chunk0028Push00 (chunk0027Push00 (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc)))))) := array_chunk0028 fuel (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail)))) (chunk0027Push00 (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc)))))
    _ = SourceJson.array (fuel + 27) (SourceJson.white (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail)))) (chunk0029Push00 (chunk0028Push00 (chunk0027Push00 (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc))))))) := array_chunk0029 fuel (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail))) (chunk0028Push00 (chunk0027Push00 (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc))))))
    _ = SourceJson.array (fuel + 26) (SourceJson.white (chunk0031Chars00 ++ (tail))) (chunk0030Push00 (chunk0029Push00 (chunk0028Push00 (chunk0027Push00 (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc)))))))) := array_chunk0030 fuel (chunk0031Chars00 ++ (tail)) (chunk0029Push00 (chunk0028Push00 (chunk0027Push00 (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc)))))))
    _ = SourceJson.array (fuel + 25) (SourceJson.white tail) (blockPush acc) := array_chunk0031 fuel (tail) (chunk0030Push00 (chunk0029Push00 (chunk0028Push00 (chunk0027Push00 (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc))))))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 92965).take 8010 = blockChars := by rfl

theorem block_original_split : sourceRest 92965 = blockChars ++ sourceRest 100975 := by
  calc
    sourceRest 92965 = (sourceRest 92965).take 8010 ++ (sourceRest 92965).drop 8010 :=
      (List.take_append_drop 8010 (sourceRest 92965)).symm
    _ = blockChars ++ (sourceRest 92965).drop 8010 :=
      congrArg (fun part => part ++ (sourceRest 92965).drop 8010) block_original_prefix
    _ = blockChars ++ sourceRest 100975 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 92965 8010)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 33) (SourceJson.white (sourceRest 92965)) acc =
      SourceJson.array (fuel + 25) (SourceJson.white (sourceRest 100975)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 33) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 100975) acc)

#print axioms value_fragment0094007
#print axioms object_fragment0094779_field_000
#print axioms object_fragment0094779_field_001
#print axioms object_fragment0094779_field_002
#print axioms object_fragment0094779_field_003
#print axioms object_fragment0094779_field_004
#print axioms value_fragment0094779
#print axioms array_fragment0096034_chunk_000
#print axioms array_fragment0096034_chunk_001
#print axioms array_fragment0096034_chunk_002
#print axioms array_fragment0096034_chunk_003
#print axioms array_fragment0096034_chunk_004
#print axioms value_fragment0096034
#print axioms object_fragment0095761_field_000
#print axioms object_fragment0095761_field_001
#print axioms object_fragment0095761_field_002
#print axioms object_fragment0095761_field_003_header
#print axioms object_fragment0095761_field_003
#print axioms object_fragment0095761_field_004
#print axioms value_fragment0095761
#print axioms array_fragment0097960_chunk_000
#print axioms array_fragment0097960_chunk_001
#print axioms array_fragment0097960_chunk_002
#print axioms array_fragment0097960_chunk_003
#print axioms value_fragment0097960
#print axioms object_fragment0097713_field_000
#print axioms object_fragment0097713_field_001
#print axioms object_fragment0097713_field_002
#print axioms object_fragment0097713_field_003_header
#print axioms object_fragment0097713_field_003
#print axioms object_fragment0097713_field_004
#print axioms value_fragment0097713
#print axioms array_fragment0100051_chunk_000
#print axioms array_fragment0100051_chunk_001
#print axioms array_fragment0100051_chunk_002
#print axioms array_fragment0100051_chunk_003
#print axioms value_fragment0100051
#print axioms object_fragment0099829_field_000
#print axioms object_fragment0099829_field_001
#print axioms object_fragment0099829_field_002
#print axioms object_fragment0099829_field_003_header
#print axioms object_fragment0099829_field_003
#print axioms object_fragment0099829_field_004
#print axioms value_fragment0099829
#print axioms array_chunk0024
#print axioms array_chunk0025
#print axioms array_chunk0026
#print axioms array_chunk0027_head
#print axioms array_chunk0027
#print axioms array_chunk0028_head
#print axioms array_chunk0028
#print axioms array_chunk0029_head
#print axioms array_chunk0029
#print axioms array_chunk0030
#print axioms array_chunk0031_head
#print axioms array_chunk0031
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end FaceLedgerBlock003

end ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
