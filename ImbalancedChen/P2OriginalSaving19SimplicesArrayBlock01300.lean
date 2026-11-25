import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock01200
import ImbalancedChen.P2OriginalSaving19ValueFragment18834000
import ImbalancedChen.P2OriginalSaving19ValueFragment18989400
import ImbalancedChen.P2OriginalSaving19ValueFragment19136300
import ImbalancedChen.P2OriginalSaving19ValueFragment19317700
import ImbalancedChen.P2OriginalSaving19GeometrySlice18833400

/-! Original simplices block 13/13. Generic small chunks are composed first; exact original bytes are then bound once for the complete block, retaining the original arbitrary tail and accumulator semantics.
Exact original bytes are candidate data; the original reader equations below
are the Lean checks. No whole-file decide or replacement reader is used. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_052_before_generic"
  err.flush

noncomputable def simplicesChunk052LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def simplicesChunk052SuffixChars00 : List Char := [',']
noncomputable def simplicesChunk052Chars00 : List Char := simplicesChunk052LeadChars00 ++ fragment188340Chars00 ++ simplicesChunk052SuffixChars00
noncomputable def simplicesChunk052Push00 (acc : List SourceJson) : List SourceJson := fragment188340Value00 :: acc

noncomputable def simplicesChunk052AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_simplices_chunk_052_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 421)
      (SourceJson.white (simplicesChunk052LeadChars00 ++ (fragment188340Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 420) (fragment188340Chars00 ++ rest)).bind
        (simplicesChunk052AfterValue00 (fuel + 420) acc) := by rfl

theorem array_simplices_chunk_052 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 421) (SourceJson.white (simplicesChunk052Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 420) (SourceJson.white tail) (simplicesChunk052Push00 acc) := by
  have hinput : simplicesChunk052Chars00 ++ tail = simplicesChunk052LeadChars00 ++ (fragment188340Chars00 ++ (simplicesChunk052SuffixChars00 ++ tail)) := by
    simp only [simplicesChunk052Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 421) (SourceJson.white (simplicesChunk052Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 421)
          (SourceJson.white (simplicesChunk052LeadChars00 ++ (fragment188340Chars00 ++ (simplicesChunk052SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 421) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 420) (fragment188340Chars00 ++ (simplicesChunk052SuffixChars00 ++ tail))).bind
        (simplicesChunk052AfterValue00 (fuel + 420) acc) := array_simplices_chunk_052_head fuel (simplicesChunk052SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment188340Value00, simplicesChunk052SuffixChars00 ++ tail)).bind
        (simplicesChunk052AfterValue00 (fuel + 420) acc) :=
      congrArg (fun result => result.bind (simplicesChunk052AfterValue00 (fuel + 420) acc))
        (value_fragment188340 (fuel + 199) (simplicesChunk052SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 420) (SourceJson.white tail) (simplicesChunk052Push00 acc) := by rfl

noncomputable def simplicesArrayAcc05300 : List SourceJson := simplicesChunk052Push00 simplicesArrayAcc05200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_052_generic_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_053_before_generic"
  err.flush

noncomputable def simplicesChunk053LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def simplicesChunk053SuffixChars00 : List Char := [',']
noncomputable def simplicesChunk053Chars00 : List Char := simplicesChunk053LeadChars00 ++ fragment189894Chars00 ++ simplicesChunk053SuffixChars00
noncomputable def simplicesChunk053Push00 (acc : List SourceJson) : List SourceJson := fragment189894Value00 :: acc

noncomputable def simplicesChunk053AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_simplices_chunk_053_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 420)
      (SourceJson.white (simplicesChunk053LeadChars00 ++ (fragment189894Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 419) (fragment189894Chars00 ++ rest)).bind
        (simplicesChunk053AfterValue00 (fuel + 419) acc) := by rfl

theorem array_simplices_chunk_053 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 420) (SourceJson.white (simplicesChunk053Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 419) (SourceJson.white tail) (simplicesChunk053Push00 acc) := by
  have hinput : simplicesChunk053Chars00 ++ tail = simplicesChunk053LeadChars00 ++ (fragment189894Chars00 ++ (simplicesChunk053SuffixChars00 ++ tail)) := by
    simp only [simplicesChunk053Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 420) (SourceJson.white (simplicesChunk053Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 420)
          (SourceJson.white (simplicesChunk053LeadChars00 ++ (fragment189894Chars00 ++ (simplicesChunk053SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 420) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 419) (fragment189894Chars00 ++ (simplicesChunk053SuffixChars00 ++ tail))).bind
        (simplicesChunk053AfterValue00 (fuel + 419) acc) := array_simplices_chunk_053_head fuel (simplicesChunk053SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment189894Value00, simplicesChunk053SuffixChars00 ++ tail)).bind
        (simplicesChunk053AfterValue00 (fuel + 419) acc) :=
      congrArg (fun result => result.bind (simplicesChunk053AfterValue00 (fuel + 419) acc))
        (value_fragment189894 (fuel + 234) (simplicesChunk053SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 419) (SourceJson.white tail) (simplicesChunk053Push00 acc) := by rfl

noncomputable def simplicesArrayAcc05400 : List SourceJson := simplicesChunk053Push00 simplicesArrayAcc05300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_053_generic_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_054_before_generic"
  err.flush

noncomputable def simplicesChunk054LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def simplicesChunk054SuffixChars00 : List Char := [',']
noncomputable def simplicesChunk054Chars00 : List Char := simplicesChunk054LeadChars00 ++ fragment191363Chars00 ++ simplicesChunk054SuffixChars00
noncomputable def simplicesChunk054Push00 (acc : List SourceJson) : List SourceJson := fragment191363Value00 :: acc

noncomputable def simplicesChunk054AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_simplices_chunk_054_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 419)
      (SourceJson.white (simplicesChunk054LeadChars00 ++ (fragment191363Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 418) (fragment191363Chars00 ++ rest)).bind
        (simplicesChunk054AfterValue00 (fuel + 418) acc) := by rfl

theorem array_simplices_chunk_054 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 419) (SourceJson.white (simplicesChunk054Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 418) (SourceJson.white tail) (simplicesChunk054Push00 acc) := by
  have hinput : simplicesChunk054Chars00 ++ tail = simplicesChunk054LeadChars00 ++ (fragment191363Chars00 ++ (simplicesChunk054SuffixChars00 ++ tail)) := by
    simp only [simplicesChunk054Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 419) (SourceJson.white (simplicesChunk054Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 419)
          (SourceJson.white (simplicesChunk054LeadChars00 ++ (fragment191363Chars00 ++ (simplicesChunk054SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 419) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 418) (fragment191363Chars00 ++ (simplicesChunk054SuffixChars00 ++ tail))).bind
        (simplicesChunk054AfterValue00 (fuel + 418) acc) := array_simplices_chunk_054_head fuel (simplicesChunk054SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment191363Value00, simplicesChunk054SuffixChars00 ++ tail)).bind
        (simplicesChunk054AfterValue00 (fuel + 418) acc) :=
      congrArg (fun result => result.bind (simplicesChunk054AfterValue00 (fuel + 418) acc))
        (value_fragment191363 (fuel + 71) (simplicesChunk054SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 418) (SourceJson.white tail) (simplicesChunk054Push00 acc) := by rfl

noncomputable def simplicesArrayAcc05500 : List SourceJson := simplicesChunk054Push00 simplicesArrayAcc05400

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_054_generic_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_055_before_generic"
  err.flush

noncomputable def simplicesChunk055LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def simplicesChunk055SuffixChars00 : List Char := ['\r', '\n', ' ', ' ', ']']
noncomputable def simplicesChunk055Chars00 : List Char := simplicesChunk055LeadChars00 ++ fragment193177Chars00 ++ simplicesChunk055SuffixChars00
noncomputable def simplicesChunk055Push00 (acc : List SourceJson) : List SourceJson := fragment193177Value00 :: acc

noncomputable def simplicesChunk055AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_simplices_chunk_055_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 418)
      (SourceJson.white (simplicesChunk055LeadChars00 ++ (fragment193177Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 417) (fragment193177Chars00 ++ rest)).bind
        (simplicesChunk055AfterValue00 (fuel + 417) acc) := by rfl

theorem array_simplices_chunk_055 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 418) (SourceJson.white (simplicesChunk055Chars00 ++ tail)) acc =
      .ok (.arr ((simplicesChunk055Push00 acc).reverse), tail) := by
  have hinput : simplicesChunk055Chars00 ++ tail = simplicesChunk055LeadChars00 ++ (fragment193177Chars00 ++ (simplicesChunk055SuffixChars00 ++ tail)) := by
    simp only [simplicesChunk055Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 418) (SourceJson.white (simplicesChunk055Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 418)
          (SourceJson.white (simplicesChunk055LeadChars00 ++ (fragment193177Chars00 ++ (simplicesChunk055SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 418) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 417) (fragment193177Chars00 ++ (simplicesChunk055SuffixChars00 ++ tail))).bind
        (simplicesChunk055AfterValue00 (fuel + 417) acc) := array_simplices_chunk_055_head fuel (simplicesChunk055SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment193177Value00, simplicesChunk055SuffixChars00 ++ tail)).bind
        (simplicesChunk055AfterValue00 (fuel + 417) acc) :=
      congrArg (fun result => result.bind (simplicesChunk055AfterValue00 (fuel + 417) acc))
        (value_fragment193177 (fuel + 175) (simplicesChunk055SuffixChars00 ++ tail))
    _ = .ok (.arr ((simplicesChunk055Push00 acc).reverse), tail) := by rfl

noncomputable def simplicesArrayAcc05600 : List SourceJson := simplicesChunk055Push00 simplicesArrayAcc05500

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_055_generic_complete"
  err.flush

noncomputable def simplicesBlock013Chars00 : List Char := simplicesChunk052Chars00 ++ simplicesChunk053Chars00 ++ simplicesChunk054Chars00 ++ simplicesChunk055Chars00
noncomputable def simplicesBlock013Push00 (acc : List SourceJson) : List SourceJson := simplicesChunk055Push00 (simplicesChunk054Push00 (simplicesChunk053Push00 (simplicesChunk052Push00 (acc))))

theorem array_simplices_block_013 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 421)
      (SourceJson.white (simplicesBlock013Chars00 ++ tail)) acc =
      .ok (.arr ((simplicesBlock013Push00 acc).reverse), tail) := by
  have hinput : simplicesBlock013Chars00 ++ tail = simplicesChunk052Chars00 ++ (simplicesChunk053Chars00 ++ (simplicesChunk054Chars00 ++ (simplicesChunk055Chars00 ++ (tail)))) := by
    simp only [simplicesBlock013Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 421)
        (SourceJson.white (simplicesBlock013Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 421) (SourceJson.white (simplicesChunk052Chars00 ++ (simplicesChunk053Chars00 ++ (simplicesChunk054Chars00 ++ (simplicesChunk055Chars00 ++ (tail)))))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 421) (SourceJson.white s) acc) hinput
    _ = SourceJson.array (fuel + 420) (SourceJson.white (simplicesChunk053Chars00 ++ (simplicesChunk054Chars00 ++ (simplicesChunk055Chars00 ++ (tail))))) (simplicesChunk052Push00 (acc)) := array_simplices_chunk_052 fuel (simplicesChunk053Chars00 ++ (simplicesChunk054Chars00 ++ (simplicesChunk055Chars00 ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 419) (SourceJson.white (simplicesChunk054Chars00 ++ (simplicesChunk055Chars00 ++ (tail)))) (simplicesChunk053Push00 (simplicesChunk052Push00 (acc))) := array_simplices_chunk_053 fuel (simplicesChunk054Chars00 ++ (simplicesChunk055Chars00 ++ (tail))) (simplicesChunk052Push00 (acc))
    _ = SourceJson.array (fuel + 418) (SourceJson.white (simplicesChunk055Chars00 ++ (tail))) (simplicesChunk054Push00 (simplicesChunk053Push00 (simplicesChunk052Push00 (acc)))) := array_simplices_chunk_054 fuel (simplicesChunk055Chars00 ++ (tail)) (simplicesChunk053Push00 (simplicesChunk052Push00 (acc)))
    _ = .ok (.arr ((simplicesBlock013Push00 acc).reverse), tail) := array_simplices_chunk_055 fuel (tail) (simplicesChunk054Push00 (simplicesChunk053Push00 (simplicesChunk052Push00 (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_block_013_before_single_binding"
  err.flush

theorem geometryChars00_simplices_block_013_prefix :
    (geometryChars00.drop 188334).take 6442 = simplicesBlock013Chars00 := by
  exact geometryChars00_slice_188334_prefix.trans (by rfl)

theorem geometryChars00_simplices_block_013_split :
    geometryChars00.drop 188334 = simplicesBlock013Chars00 ++ geometryChars00.drop 194776 := by
  calc
    geometryChars00.drop 188334 =
        (geometryChars00.drop 188334).take 6442 ++ (geometryChars00.drop 188334).drop 6442 :=
      (List.take_append_drop 6442 (geometryChars00.drop 188334)).symm
    _ = simplicesBlock013Chars00 ++ (geometryChars00.drop 188334).drop 6442 :=
      congrArg (fun p => p ++ (geometryChars00.drop 188334).drop 6442) geometryChars00_simplices_block_013_prefix
    _ = simplicesBlock013Chars00 ++ geometryChars00.drop 194776 := by rw [List.drop_drop]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_block_013_after_single_binding"
  err.flush

theorem array_simplices_original_block_013 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 421)
      (SourceJson.white (geometryChars00.drop 188334)) acc =
      .ok (.arr ((simplicesBlock013Push00 acc).reverse), geometryChars00.drop 194776) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 421) (SourceJson.white s) acc)
      geometryChars00_simplices_block_013_split).trans (array_simplices_block_013 fuel (geometryChars00.drop 194776) acc)

noncomputable def simplicesArrayValue00 : SourceJson := .arr (simplicesArrayAcc05600.reverse)

theorem simplices_array_through_block_013 (fuel : Nat) :
    SourceJson.array (fuel + 473)
      (SourceJson.white (geometryChars00.drop 100434)) [] =
      .ok (simplicesArrayValue00, geometryChars00.drop 194776) := by
  exact (simplices_array_through_block_012 fuel).trans
    (array_simplices_original_block_013 fuel simplicesArrayAcc05200)

theorem value_simplices_original (fuel : Nat) :
    SourceJson.value (fuel + 474) (geometryChars00.drop 100433) =
      .ok (simplicesArrayValue00, geometryChars00.drop 194776) := by
  exact (value_simplices_open fuel).trans (simplices_array_through_block_013 fuel)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_block_013_complete"
  err.flush

#print axioms array_simplices_chunk_052_head
#print axioms array_simplices_chunk_052
#print axioms array_simplices_chunk_053_head
#print axioms array_simplices_chunk_053
#print axioms array_simplices_chunk_054_head
#print axioms array_simplices_chunk_054
#print axioms array_simplices_chunk_055_head
#print axioms array_simplices_chunk_055
#print axioms array_simplices_block_013
#print axioms geometryChars00_simplices_block_013_prefix
#print axioms geometryChars00_simplices_block_013_split
#print axioms array_simplices_original_block_013
#print axioms simplices_array_through_block_013
#print axioms value_simplices_original

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
