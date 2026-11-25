import ImbalancedChen.P2OriginalSaving19SourceJson

/-! Self-delimiting original value fragment, raw candidate span [67480,68343). This owner is independent of geometryChars00; its arbitrary-tail theorem can be reused after a separately proved byte binding.
Exact original bytes are candidate data; the original reader equations below
are the Lean checks. No whole-file decide or replacement reader is used. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def fragment067480Acc00000 : List SourceJson := []

noncomputable def fragment067480Chunk000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment067480Chunk000Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['8']), .number (String.ofList ['9'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7'])]) :: (acc))

theorem array_fragment067480_chunk_000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 17) (SourceJson.white (fragment067480Chunk000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 15) (SourceJson.white tail) (fragment067480Chunk000Push00 acc) := by
  rfl

noncomputable def fragment067480Acc00100 : List SourceJson := fragment067480Chunk000Push00 fragment067480Acc00000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment067480_array_chunk_000"
  err.flush

noncomputable def fragment067480Chunk001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment067480Chunk001Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9'])]) :: (acc))

theorem array_fragment067480_chunk_001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 15) (SourceJson.white (fragment067480Chunk001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 13) (SourceJson.white tail) (fragment067480Chunk001Push00 acc) := by
  rfl

noncomputable def fragment067480Acc00200 : List SourceJson := fragment067480Chunk001Push00 fragment067480Acc00100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment067480_array_chunk_001"
  err.flush

noncomputable def fragment067480Chunk002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment067480Chunk002Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['8'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['7']), .number (String.ofList ['9'])]) :: (acc))

theorem array_fragment067480_chunk_002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 13) (SourceJson.white (fragment067480Chunk002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 11) (SourceJson.white tail) (fragment067480Chunk002Push00 acc) := by
  rfl

noncomputable def fragment067480Acc00300 : List SourceJson := fragment067480Chunk002Push00 fragment067480Acc00200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment067480_array_chunk_002"
  err.flush

noncomputable def fragment067480Chunk003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']']
noncomputable def fragment067480Chunk003Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9'])]) :: (acc)

theorem array_fragment067480_chunk_003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 11) (SourceJson.white (fragment067480Chunk003Chars00 ++ tail)) acc =
      .ok (.arr ((fragment067480Chunk003Push00 acc).reverse), tail) := by
  rfl

noncomputable def fragment067480Acc00400 : List SourceJson := fragment067480Chunk003Push00 fragment067480Acc00300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment067480_array_chunk_003"
  err.flush

noncomputable def fragment067480Chars00 : List Char := '[' :: (fragment067480Chunk000Chars00 ++ fragment067480Chunk001Chars00 ++ fragment067480Chunk002Chars00 ++ fragment067480Chunk003Chars00)
noncomputable def fragment067480Value00 : SourceJson := .arr (fragment067480Acc00400.reverse)

theorem value_fragment067480 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 18) (fragment067480Chars00 ++ tail) =
      .ok (fragment067480Value00, tail) := by
  have hinput : fragment067480Chars00 ++ tail = '[' :: (fragment067480Chunk000Chars00 ++ (fragment067480Chunk001Chars00 ++ (fragment067480Chunk002Chars00 ++ (fragment067480Chunk003Chars00 ++ (tail))))) := by
    simp only [fragment067480Chars00, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 18) (fragment067480Chars00 ++ tail) =
        SourceJson.value (fuel + 18) ('[' :: (fragment067480Chunk000Chars00 ++ (fragment067480Chunk001Chars00 ++ (fragment067480Chunk002Chars00 ++ (fragment067480Chunk003Chars00 ++ (tail)))))) :=
      congrArg (SourceJson.value (fuel + 18)) hinput
    _ = SourceJson.array (fuel + 17) (SourceJson.white (fragment067480Chunk000Chars00 ++ (fragment067480Chunk001Chars00 ++ (fragment067480Chunk002Chars00 ++ (fragment067480Chunk003Chars00 ++ (tail)))))) fragment067480Acc00000 := by rfl
    _ = SourceJson.array (fuel + 15) (SourceJson.white (fragment067480Chunk001Chars00 ++ (fragment067480Chunk002Chars00 ++ (fragment067480Chunk003Chars00 ++ (tail))))) fragment067480Acc00100 := array_fragment067480_chunk_000 fuel (fragment067480Chunk001Chars00 ++ (fragment067480Chunk002Chars00 ++ (fragment067480Chunk003Chars00 ++ (tail)))) fragment067480Acc00000
    _ = SourceJson.array (fuel + 13) (SourceJson.white (fragment067480Chunk002Chars00 ++ (fragment067480Chunk003Chars00 ++ (tail)))) fragment067480Acc00200 := array_fragment067480_chunk_001 fuel (fragment067480Chunk002Chars00 ++ (fragment067480Chunk003Chars00 ++ (tail))) fragment067480Acc00100
    _ = SourceJson.array (fuel + 11) (SourceJson.white (fragment067480Chunk003Chars00 ++ (tail))) fragment067480Acc00300 := array_fragment067480_chunk_002 fuel (fragment067480Chunk003Chars00 ++ (tail)) fragment067480Acc00200
    _ = .ok (fragment067480Value00, tail) := array_fragment067480_chunk_003 fuel (tail) fragment067480Acc00300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment067480_value_complete"
  err.flush

#print axioms array_fragment067480_chunk_000
#print axioms array_fragment067480_chunk_001
#print axioms array_fragment067480_chunk_002
#print axioms array_fragment067480_chunk_003
#print axioms value_fragment067480

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
