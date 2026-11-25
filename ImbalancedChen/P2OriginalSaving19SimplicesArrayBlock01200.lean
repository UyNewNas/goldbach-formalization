import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock01100
import ImbalancedChen.P2OriginalSaving19ValueFragment18192700
import ImbalancedChen.P2OriginalSaving19ValueFragment18358700
import ImbalancedChen.P2OriginalSaving19ValueFragment18519800
import ImbalancedChen.P2OriginalSaving19ValueFragment18677300

/-! Original simplices block 12/13. Generic small chunks are composed first; exact original bytes are then bound once for the complete block, retaining the original arbitrary tail and accumulator semantics.
Exact original bytes are candidate data; the original reader equations below
are the Lean checks. No whole-file decide or replacement reader is used. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_048_before_generic"
  err.flush

noncomputable def simplicesChunk048LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def simplicesChunk048SuffixChars00 : List Char := [',']
noncomputable def simplicesChunk048Chars00 : List Char := simplicesChunk048LeadChars00 ++ fragment181927Chars00 ++ simplicesChunk048SuffixChars00
noncomputable def simplicesChunk048Push00 (acc : List SourceJson) : List SourceJson := fragment181927Value00 :: acc

noncomputable def simplicesChunk048AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_simplices_chunk_048_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 425)
      (SourceJson.white (simplicesChunk048LeadChars00 ++ (fragment181927Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 424) (fragment181927Chars00 ++ rest)).bind
        (simplicesChunk048AfterValue00 (fuel + 424) acc) := by rfl

theorem array_simplices_chunk_048 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 425) (SourceJson.white (simplicesChunk048Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 424) (SourceJson.white tail) (simplicesChunk048Push00 acc) := by
  have hinput : simplicesChunk048Chars00 ++ tail = simplicesChunk048LeadChars00 ++ (fragment181927Chars00 ++ (simplicesChunk048SuffixChars00 ++ tail)) := by
    simp only [simplicesChunk048Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 425) (SourceJson.white (simplicesChunk048Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 425)
          (SourceJson.white (simplicesChunk048LeadChars00 ++ (fragment181927Chars00 ++ (simplicesChunk048SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 425) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 424) (fragment181927Chars00 ++ (simplicesChunk048SuffixChars00 ++ tail))).bind
        (simplicesChunk048AfterValue00 (fuel + 424) acc) := array_simplices_chunk_048_head fuel (simplicesChunk048SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment181927Value00, simplicesChunk048SuffixChars00 ++ tail)).bind
        (simplicesChunk048AfterValue00 (fuel + 424) acc) :=
      congrArg (fun result => result.bind (simplicesChunk048AfterValue00 (fuel + 424) acc))
        (value_fragment181927 (fuel + 156) (simplicesChunk048SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 424) (SourceJson.white tail) (simplicesChunk048Push00 acc) := by rfl

noncomputable def simplicesArrayAcc04900 : List SourceJson := simplicesChunk048Push00 simplicesArrayAcc04800

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_048_generic_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_049_before_generic"
  err.flush

noncomputable def simplicesChunk049LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def simplicesChunk049SuffixChars00 : List Char := [',']
noncomputable def simplicesChunk049Chars00 : List Char := simplicesChunk049LeadChars00 ++ fragment183587Chars00 ++ simplicesChunk049SuffixChars00
noncomputable def simplicesChunk049Push00 (acc : List SourceJson) : List SourceJson := fragment183587Value00 :: acc

noncomputable def simplicesChunk049AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_simplices_chunk_049_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 424)
      (SourceJson.white (simplicesChunk049LeadChars00 ++ (fragment183587Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 423) (fragment183587Chars00 ++ rest)).bind
        (simplicesChunk049AfterValue00 (fuel + 423) acc) := by rfl

theorem array_simplices_chunk_049 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 424) (SourceJson.white (simplicesChunk049Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 423) (SourceJson.white tail) (simplicesChunk049Push00 acc) := by
  have hinput : simplicesChunk049Chars00 ++ tail = simplicesChunk049LeadChars00 ++ (fragment183587Chars00 ++ (simplicesChunk049SuffixChars00 ++ tail)) := by
    simp only [simplicesChunk049Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 424) (SourceJson.white (simplicesChunk049Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 424)
          (SourceJson.white (simplicesChunk049LeadChars00 ++ (fragment183587Chars00 ++ (simplicesChunk049SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 424) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 423) (fragment183587Chars00 ++ (simplicesChunk049SuffixChars00 ++ tail))).bind
        (simplicesChunk049AfterValue00 (fuel + 423) acc) := array_simplices_chunk_049_head fuel (simplicesChunk049SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment183587Value00, simplicesChunk049SuffixChars00 ++ tail)).bind
        (simplicesChunk049AfterValue00 (fuel + 423) acc) :=
      congrArg (fun result => result.bind (simplicesChunk049AfterValue00 (fuel + 423) acc))
        (value_fragment183587 (fuel + 177) (simplicesChunk049SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 423) (SourceJson.white tail) (simplicesChunk049Push00 acc) := by rfl

noncomputable def simplicesArrayAcc05000 : List SourceJson := simplicesChunk049Push00 simplicesArrayAcc04900

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_049_generic_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_050_before_generic"
  err.flush

noncomputable def simplicesChunk050LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def simplicesChunk050SuffixChars00 : List Char := [',']
noncomputable def simplicesChunk050Chars00 : List Char := simplicesChunk050LeadChars00 ++ fragment185198Chars00 ++ simplicesChunk050SuffixChars00
noncomputable def simplicesChunk050Push00 (acc : List SourceJson) : List SourceJson := fragment185198Value00 :: acc

noncomputable def simplicesChunk050AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_simplices_chunk_050_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 423)
      (SourceJson.white (simplicesChunk050LeadChars00 ++ (fragment185198Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 422) (fragment185198Chars00 ++ rest)).bind
        (simplicesChunk050AfterValue00 (fuel + 422) acc) := by rfl

theorem array_simplices_chunk_050 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 423) (SourceJson.white (simplicesChunk050Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 422) (SourceJson.white tail) (simplicesChunk050Push00 acc) := by
  have hinput : simplicesChunk050Chars00 ++ tail = simplicesChunk050LeadChars00 ++ (fragment185198Chars00 ++ (simplicesChunk050SuffixChars00 ++ tail)) := by
    simp only [simplicesChunk050Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 423) (SourceJson.white (simplicesChunk050Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 423)
          (SourceJson.white (simplicesChunk050LeadChars00 ++ (fragment185198Chars00 ++ (simplicesChunk050SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 423) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 422) (fragment185198Chars00 ++ (simplicesChunk050SuffixChars00 ++ tail))).bind
        (simplicesChunk050AfterValue00 (fuel + 422) acc) := array_simplices_chunk_050_head fuel (simplicesChunk050SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment185198Value00, simplicesChunk050SuffixChars00 ++ tail)).bind
        (simplicesChunk050AfterValue00 (fuel + 422) acc) :=
      congrArg (fun result => result.bind (simplicesChunk050AfterValue00 (fuel + 422) acc))
        (value_fragment185198 (fuel + 194) (simplicesChunk050SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 422) (SourceJson.white tail) (simplicesChunk050Push00 acc) := by rfl

noncomputable def simplicesArrayAcc05100 : List SourceJson := simplicesChunk050Push00 simplicesArrayAcc05000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_050_generic_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_051_before_generic"
  err.flush

noncomputable def simplicesChunk051LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def simplicesChunk051SuffixChars00 : List Char := [',']
noncomputable def simplicesChunk051Chars00 : List Char := simplicesChunk051LeadChars00 ++ fragment186773Chars00 ++ simplicesChunk051SuffixChars00
noncomputable def simplicesChunk051Push00 (acc : List SourceJson) : List SourceJson := fragment186773Value00 :: acc

noncomputable def simplicesChunk051AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_simplices_chunk_051_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 422)
      (SourceJson.white (simplicesChunk051LeadChars00 ++ (fragment186773Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 421) (fragment186773Chars00 ++ rest)).bind
        (simplicesChunk051AfterValue00 (fuel + 421) acc) := by rfl

theorem array_simplices_chunk_051 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 422) (SourceJson.white (simplicesChunk051Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 421) (SourceJson.white tail) (simplicesChunk051Push00 acc) := by
  have hinput : simplicesChunk051Chars00 ++ tail = simplicesChunk051LeadChars00 ++ (fragment186773Chars00 ++ (simplicesChunk051SuffixChars00 ++ tail)) := by
    simp only [simplicesChunk051Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 422) (SourceJson.white (simplicesChunk051Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 422)
          (SourceJson.white (simplicesChunk051LeadChars00 ++ (fragment186773Chars00 ++ (simplicesChunk051SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 422) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 421) (fragment186773Chars00 ++ (simplicesChunk051SuffixChars00 ++ tail))).bind
        (simplicesChunk051AfterValue00 (fuel + 421) acc) := array_simplices_chunk_051_head fuel (simplicesChunk051SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment186773Value00, simplicesChunk051SuffixChars00 ++ tail)).bind
        (simplicesChunk051AfterValue00 (fuel + 421) acc) :=
      congrArg (fun result => result.bind (simplicesChunk051AfterValue00 (fuel + 421) acc))
        (value_fragment186773 (fuel + 204) (simplicesChunk051SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 421) (SourceJson.white tail) (simplicesChunk051Push00 acc) := by rfl

noncomputable def simplicesArrayAcc05200 : List SourceJson := simplicesChunk051Push00 simplicesArrayAcc05100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_051_generic_complete"
  err.flush

noncomputable def simplicesBlock012Chars00 : List Char := simplicesChunk048Chars00 ++ simplicesChunk049Chars00 ++ simplicesChunk050Chars00 ++ simplicesChunk051Chars00
noncomputable def simplicesBlock012Push00 (acc : List SourceJson) : List SourceJson := simplicesChunk051Push00 (simplicesChunk050Push00 (simplicesChunk049Push00 (simplicesChunk048Push00 (acc))))

theorem array_simplices_block_012 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 425)
      (SourceJson.white (simplicesBlock012Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 421) (SourceJson.white tail) (simplicesBlock012Push00 acc) := by
  have hinput : simplicesBlock012Chars00 ++ tail = simplicesChunk048Chars00 ++ (simplicesChunk049Chars00 ++ (simplicesChunk050Chars00 ++ (simplicesChunk051Chars00 ++ (tail)))) := by
    simp only [simplicesBlock012Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 425)
        (SourceJson.white (simplicesBlock012Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 425) (SourceJson.white (simplicesChunk048Chars00 ++ (simplicesChunk049Chars00 ++ (simplicesChunk050Chars00 ++ (simplicesChunk051Chars00 ++ (tail)))))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 425) (SourceJson.white s) acc) hinput
    _ = SourceJson.array (fuel + 424) (SourceJson.white (simplicesChunk049Chars00 ++ (simplicesChunk050Chars00 ++ (simplicesChunk051Chars00 ++ (tail))))) (simplicesChunk048Push00 (acc)) := array_simplices_chunk_048 fuel (simplicesChunk049Chars00 ++ (simplicesChunk050Chars00 ++ (simplicesChunk051Chars00 ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 423) (SourceJson.white (simplicesChunk050Chars00 ++ (simplicesChunk051Chars00 ++ (tail)))) (simplicesChunk049Push00 (simplicesChunk048Push00 (acc))) := array_simplices_chunk_049 fuel (simplicesChunk050Chars00 ++ (simplicesChunk051Chars00 ++ (tail))) (simplicesChunk048Push00 (acc))
    _ = SourceJson.array (fuel + 422) (SourceJson.white (simplicesChunk051Chars00 ++ (tail))) (simplicesChunk050Push00 (simplicesChunk049Push00 (simplicesChunk048Push00 (acc)))) := array_simplices_chunk_050 fuel (simplicesChunk051Chars00 ++ (tail)) (simplicesChunk049Push00 (simplicesChunk048Push00 (acc)))
    _ = SourceJson.array (fuel + 421) (SourceJson.white tail) (simplicesBlock012Push00 acc) := array_simplices_chunk_051 fuel (tail) (simplicesChunk050Push00 (simplicesChunk049Push00 (simplicesChunk048Push00 (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_block_012_before_single_binding"
  err.flush

theorem geometryChars00_simplices_block_012_prefix :
    (geometryChars00.drop 181921).take 6413 = simplicesBlock012Chars00 := by rfl

theorem geometryChars00_simplices_block_012_split :
    geometryChars00.drop 181921 = simplicesBlock012Chars00 ++ geometryChars00.drop 188334 := by
  calc
    geometryChars00.drop 181921 =
        (geometryChars00.drop 181921).take 6413 ++ (geometryChars00.drop 181921).drop 6413 :=
      (List.take_append_drop 6413 (geometryChars00.drop 181921)).symm
    _ = simplicesBlock012Chars00 ++ (geometryChars00.drop 181921).drop 6413 :=
      congrArg (fun p => p ++ (geometryChars00.drop 181921).drop 6413) geometryChars00_simplices_block_012_prefix
    _ = simplicesBlock012Chars00 ++ geometryChars00.drop 188334 := by rw [List.drop_drop]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_block_012_after_single_binding"
  err.flush

theorem array_simplices_original_block_012 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 425)
      (SourceJson.white (geometryChars00.drop 181921)) acc =
      SourceJson.array (fuel + 421)
        (SourceJson.white (geometryChars00.drop 188334)) (simplicesBlock012Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 425) (SourceJson.white s) acc)
      geometryChars00_simplices_block_012_split).trans (array_simplices_block_012 fuel (geometryChars00.drop 188334) acc)

theorem simplices_array_through_block_012 (fuel : Nat) :
    SourceJson.array (fuel + 473)
      (SourceJson.white (geometryChars00.drop 100434)) [] =
      SourceJson.array (fuel + 421)
        (SourceJson.white (geometryChars00.drop 188334)) simplicesArrayAcc05200 := by
  exact (simplices_array_through_block_011 fuel).trans
    (array_simplices_original_block_012 fuel simplicesArrayAcc04800)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_block_012_complete"
  err.flush

#print axioms array_simplices_chunk_048_head
#print axioms array_simplices_chunk_048
#print axioms array_simplices_chunk_049_head
#print axioms array_simplices_chunk_049
#print axioms array_simplices_chunk_050_head
#print axioms array_simplices_chunk_050
#print axioms array_simplices_chunk_051_head
#print axioms array_simplices_chunk_051
#print axioms array_simplices_block_012
#print axioms geometryChars00_simplices_block_012_prefix
#print axioms geometryChars00_simplices_block_012_split
#print axioms array_simplices_original_block_012
#print axioms simplices_array_through_block_012

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
