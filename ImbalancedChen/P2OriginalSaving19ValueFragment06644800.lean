import ImbalancedChen.P2OriginalSaving19SourceJson

/-! Self-delimiting original value fragment, raw candidate span [66448,67258). This owner is independent of geometryChars00; its arbitrary-tail theorem can be reused after a separately proved byte binding.
Exact original bytes are candidate data; the original reader equations below
are the Lean checks. No whole-file decide or replacement reader is used. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def fragment066448Acc00000 : List (String × SourceJson) := []

noncomputable def fragment066448Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment066448Field000Value00 : SourceJson := .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7'])]
noncomputable def fragment066448Acc00100 : List (String × SourceJson) := (fragment066448Field000Key00, fragment066448Field000Value00) :: fragment066448Acc00000
noncomputable def fragment066448Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment066448_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 19) (SourceJson.white (fragment066448Field000Chars00 ++ tail)) fragment066448Acc00000 =
      SourceJson.object (fuel + 18) (SourceJson.white tail) fragment066448Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment066448_object_field_000"
  err.flush

noncomputable def fragment066448Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment066448Field001Value00 : SourceJson := .number (String.ofList ['4'])
noncomputable def fragment066448Acc00200 : List (String × SourceJson) := (fragment066448Field001Key00, fragment066448Field001Value00) :: fragment066448Acc00100
noncomputable def fragment066448Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '4', ',']

theorem object_fragment066448_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 18) (SourceJson.white (fragment066448Field001Chars00 ++ tail)) fragment066448Acc00100 =
      SourceJson.object (fuel + 17) (SourceJson.white tail) fragment066448Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment066448_object_field_001"
  err.flush

noncomputable def fragment066448Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment066448Field002Value00 : SourceJson := .number (String.ofList ['7'])
noncomputable def fragment066448Acc00300 : List (String × SourceJson) := (fragment066448Field002Key00, fragment066448Field002Value00) :: fragment066448Acc00200
noncomputable def fragment066448Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '7', ',']

theorem object_fragment066448_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 17) (SourceJson.white (fragment066448Field002Chars00 ++ tail)) fragment066448Acc00200 =
      SourceJson.object (fuel + 16) (SourceJson.white tail) fragment066448Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment066448_object_field_002"
  err.flush

noncomputable def fragment066448Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment066448Field003Value00 : SourceJson := .arr [.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['6']), .number (String.ofList ['7'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['7'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['6'])], .arr [.number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7'])]]
noncomputable def fragment066448Acc00400 : List (String × SourceJson) := (fragment066448Field003Key00, fragment066448Field003Value00) :: fragment066448Acc00300
noncomputable def fragment066448Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment066448_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 16) (SourceJson.white (fragment066448Field003Chars00 ++ tail)) fragment066448Acc00300 =
      SourceJson.object (fuel + 15) (SourceJson.white tail) fragment066448Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment066448_object_field_003"
  err.flush

noncomputable def fragment066448Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment066448Field004Value00 : SourceJson := .number (String.ofList ['4'])
noncomputable def fragment066448Acc00500 : List (String × SourceJson) := (fragment066448Field004Key00, fragment066448Field004Value00) :: fragment066448Acc00400
noncomputable def fragment066448Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment066448_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 15) (SourceJson.white (fragment066448Field004Chars00 ++ tail)) fragment066448Acc00400 =
      .ok (.obj (fragment066448Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment066448_object_field_004"
  err.flush

noncomputable def fragment066448Chars00 : List Char := '{' :: (fragment066448Field000Chars00 ++ fragment066448Field001Chars00 ++ fragment066448Field002Chars00 ++ fragment066448Field003Chars00 ++ fragment066448Field004Chars00)
noncomputable def fragment066448Value00 : SourceJson := .obj (fragment066448Acc00500.reverse)

theorem value_fragment066448 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 20) (fragment066448Chars00 ++ tail) =
      .ok (fragment066448Value00, tail) := by
  have hinput : fragment066448Chars00 ++ tail = '{' :: (fragment066448Field000Chars00 ++ (fragment066448Field001Chars00 ++ (fragment066448Field002Chars00 ++ (fragment066448Field003Chars00 ++ (fragment066448Field004Chars00 ++ (tail)))))) := by
    simp only [fragment066448Chars00, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 20) (fragment066448Chars00 ++ tail) =
        SourceJson.value (fuel + 20) ('{' :: (fragment066448Field000Chars00 ++ (fragment066448Field001Chars00 ++ (fragment066448Field002Chars00 ++ (fragment066448Field003Chars00 ++ (fragment066448Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 20)) hinput
    _ = SourceJson.object (fuel + 19) (SourceJson.white (fragment066448Field000Chars00 ++ (fragment066448Field001Chars00 ++ (fragment066448Field002Chars00 ++ (fragment066448Field003Chars00 ++ (fragment066448Field004Chars00 ++ (tail))))))) fragment066448Acc00000 := by rfl
    _ = SourceJson.object (fuel + 18) (SourceJson.white (fragment066448Field001Chars00 ++ (fragment066448Field002Chars00 ++ (fragment066448Field003Chars00 ++ (fragment066448Field004Chars00 ++ (tail)))))) fragment066448Acc00100 := object_fragment066448_field_000 fuel (fragment066448Field001Chars00 ++ (fragment066448Field002Chars00 ++ (fragment066448Field003Chars00 ++ (fragment066448Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 17) (SourceJson.white (fragment066448Field002Chars00 ++ (fragment066448Field003Chars00 ++ (fragment066448Field004Chars00 ++ (tail))))) fragment066448Acc00200 := object_fragment066448_field_001 fuel (fragment066448Field002Chars00 ++ (fragment066448Field003Chars00 ++ (fragment066448Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 16) (SourceJson.white (fragment066448Field003Chars00 ++ (fragment066448Field004Chars00 ++ (tail)))) fragment066448Acc00300 := object_fragment066448_field_002 fuel (fragment066448Field003Chars00 ++ (fragment066448Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 15) (SourceJson.white (fragment066448Field004Chars00 ++ (tail))) fragment066448Acc00400 := object_fragment066448_field_003 fuel (fragment066448Field004Chars00 ++ (tail))
    _ = .ok (fragment066448Value00, tail) := object_fragment066448_field_004 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment066448_value_complete"
  err.flush

#print axioms object_fragment066448_field_000
#print axioms object_fragment066448_field_001
#print axioms object_fragment066448_field_002
#print axioms object_fragment066448_field_003
#print axioms object_fragment066448_field_004
#print axioms value_fragment066448

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
