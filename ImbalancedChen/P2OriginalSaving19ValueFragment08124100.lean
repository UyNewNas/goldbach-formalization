import ImbalancedChen.P2OriginalSaving19SourceJson

/-! Self-delimiting original value fragment, raw candidate span [81241,82051). This owner is independent of geometryChars00; its arbitrary-tail theorem can be reused after a separately proved byte binding.
Exact original bytes are candidate data; the original reader equations below
are the Lean checks. No whole-file decide or replacement reader is used. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def fragment081241Acc00000 : List (String × SourceJson) := []

noncomputable def fragment081241Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment081241Field000Value00 : SourceJson := .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['8']), .number (String.ofList ['9'])]
noncomputable def fragment081241Acc00100 : List (String × SourceJson) := (fragment081241Field000Key00, fragment081241Field000Value00) :: fragment081241Acc00000
noncomputable def fragment081241Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment081241_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 19) (SourceJson.white (fragment081241Field000Chars00 ++ tail)) fragment081241Acc00000 =
      SourceJson.object (fuel + 18) (SourceJson.white tail) fragment081241Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment081241_object_field_000"
  err.flush

noncomputable def fragment081241Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment081241Field001Value00 : SourceJson := .number (String.ofList ['4'])
noncomputable def fragment081241Acc00200 : List (String × SourceJson) := (fragment081241Field001Key00, fragment081241Field001Value00) :: fragment081241Acc00100
noncomputable def fragment081241Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '4', ',']

theorem object_fragment081241_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 18) (SourceJson.white (fragment081241Field001Chars00 ++ tail)) fragment081241Acc00100 =
      SourceJson.object (fuel + 17) (SourceJson.white tail) fragment081241Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment081241_object_field_001"
  err.flush

noncomputable def fragment081241Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment081241Field002Value00 : SourceJson := .number (String.ofList ['9'])
noncomputable def fragment081241Acc00300 : List (String × SourceJson) := (fragment081241Field002Key00, fragment081241Field002Value00) :: fragment081241Acc00200
noncomputable def fragment081241Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '9', ',']

theorem object_fragment081241_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 17) (SourceJson.white (fragment081241Field002Chars00 ++ tail)) fragment081241Acc00200 =
      SourceJson.object (fuel + 16) (SourceJson.white tail) fragment081241Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment081241_object_field_002"
  err.flush

noncomputable def fragment081241Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment081241Field003Value00 : SourceJson := .arr [.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['8']), .number (String.ofList ['9'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['8']), .number (String.ofList ['9'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['9'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['8'])], .arr [.number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['8']), .number (String.ofList ['9'])]]
noncomputable def fragment081241Acc00400 : List (String × SourceJson) := (fragment081241Field003Key00, fragment081241Field003Value00) :: fragment081241Acc00300
noncomputable def fragment081241Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment081241_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 16) (SourceJson.white (fragment081241Field003Chars00 ++ tail)) fragment081241Acc00300 =
      SourceJson.object (fuel + 15) (SourceJson.white tail) fragment081241Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment081241_object_field_003"
  err.flush

noncomputable def fragment081241Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment081241Field004Value00 : SourceJson := .number (String.ofList ['4'])
noncomputable def fragment081241Acc00500 : List (String × SourceJson) := (fragment081241Field004Key00, fragment081241Field004Value00) :: fragment081241Acc00400
noncomputable def fragment081241Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment081241_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 15) (SourceJson.white (fragment081241Field004Chars00 ++ tail)) fragment081241Acc00400 =
      .ok (.obj (fragment081241Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment081241_object_field_004"
  err.flush

noncomputable def fragment081241Chars00 : List Char := '{' :: (fragment081241Field000Chars00 ++ fragment081241Field001Chars00 ++ fragment081241Field002Chars00 ++ fragment081241Field003Chars00 ++ fragment081241Field004Chars00)
noncomputable def fragment081241Value00 : SourceJson := .obj (fragment081241Acc00500.reverse)

theorem value_fragment081241 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 20) (fragment081241Chars00 ++ tail) =
      .ok (fragment081241Value00, tail) := by
  have hinput : fragment081241Chars00 ++ tail = '{' :: (fragment081241Field000Chars00 ++ (fragment081241Field001Chars00 ++ (fragment081241Field002Chars00 ++ (fragment081241Field003Chars00 ++ (fragment081241Field004Chars00 ++ (tail)))))) := by
    simp only [fragment081241Chars00, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 20) (fragment081241Chars00 ++ tail) =
        SourceJson.value (fuel + 20) ('{' :: (fragment081241Field000Chars00 ++ (fragment081241Field001Chars00 ++ (fragment081241Field002Chars00 ++ (fragment081241Field003Chars00 ++ (fragment081241Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 20)) hinput
    _ = SourceJson.object (fuel + 19) (SourceJson.white (fragment081241Field000Chars00 ++ (fragment081241Field001Chars00 ++ (fragment081241Field002Chars00 ++ (fragment081241Field003Chars00 ++ (fragment081241Field004Chars00 ++ (tail))))))) fragment081241Acc00000 := by rfl
    _ = SourceJson.object (fuel + 18) (SourceJson.white (fragment081241Field001Chars00 ++ (fragment081241Field002Chars00 ++ (fragment081241Field003Chars00 ++ (fragment081241Field004Chars00 ++ (tail)))))) fragment081241Acc00100 := object_fragment081241_field_000 fuel (fragment081241Field001Chars00 ++ (fragment081241Field002Chars00 ++ (fragment081241Field003Chars00 ++ (fragment081241Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 17) (SourceJson.white (fragment081241Field002Chars00 ++ (fragment081241Field003Chars00 ++ (fragment081241Field004Chars00 ++ (tail))))) fragment081241Acc00200 := object_fragment081241_field_001 fuel (fragment081241Field002Chars00 ++ (fragment081241Field003Chars00 ++ (fragment081241Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 16) (SourceJson.white (fragment081241Field003Chars00 ++ (fragment081241Field004Chars00 ++ (tail)))) fragment081241Acc00300 := object_fragment081241_field_002 fuel (fragment081241Field003Chars00 ++ (fragment081241Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 15) (SourceJson.white (fragment081241Field004Chars00 ++ (tail))) fragment081241Acc00400 := object_fragment081241_field_003 fuel (fragment081241Field004Chars00 ++ (tail))
    _ = .ok (fragment081241Value00, tail) := object_fragment081241_field_004 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment081241_value_complete"
  err.flush

#print axioms object_fragment081241_field_000
#print axioms object_fragment081241_field_001
#print axioms object_fragment081241_field_002
#print axioms object_fragment081241_field_003
#print axioms object_fragment081241_field_004
#print axioms value_fragment081241

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
