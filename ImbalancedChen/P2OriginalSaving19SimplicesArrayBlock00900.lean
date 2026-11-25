import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00800
import ImbalancedChen.P2OriginalSaving19ValueFragment16192700
import ImbalancedChen.P2OriginalSaving19ValueFragment16356100
import ImbalancedChen.P2OriginalSaving19ValueFragment16514800
import ImbalancedChen.P2OriginalSaving19ValueFragment16673900

/-! Original simplices block 9/13. Generic small chunks are composed first; exact original bytes are then bound once for the complete block, retaining the original arbitrary tail and accumulator semantics.
Exact original bytes are candidate data; the original reader equations below
are the Lean checks. No whole-file decide or replacement reader is used. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_036_before_generic"
  err.flush

noncomputable def simplicesChunk036LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def simplicesChunk036SuffixChars00 : List Char := [',']
noncomputable def simplicesChunk036Chars00 : List Char := simplicesChunk036LeadChars00 ++ fragment161927Chars00 ++ simplicesChunk036SuffixChars00
noncomputable def simplicesChunk036Push00 (acc : List SourceJson) : List SourceJson := fragment161927Value00 :: acc

noncomputable def simplicesChunk036AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_simplices_chunk_036_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 437)
      (SourceJson.white (simplicesChunk036LeadChars00 ++ (fragment161927Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 436) (fragment161927Chars00 ++ rest)).bind
        (simplicesChunk036AfterValue00 (fuel + 436) acc) := by rfl

theorem array_simplices_chunk_036 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 437) (SourceJson.white (simplicesChunk036Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 436) (SourceJson.white tail) (simplicesChunk036Push00 acc) := by
  have hinput : simplicesChunk036Chars00 ++ tail = simplicesChunk036LeadChars00 ++ (fragment161927Chars00 ++ (simplicesChunk036SuffixChars00 ++ tail)) := by
    simp only [simplicesChunk036Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 437) (SourceJson.white (simplicesChunk036Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 437)
          (SourceJson.white (simplicesChunk036LeadChars00 ++ (fragment161927Chars00 ++ (simplicesChunk036SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 437) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 436) (fragment161927Chars00 ++ (simplicesChunk036SuffixChars00 ++ tail))).bind
        (simplicesChunk036AfterValue00 (fuel + 436) acc) := array_simplices_chunk_036_head fuel (simplicesChunk036SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment161927Value00, simplicesChunk036SuffixChars00 ++ tail)).bind
        (simplicesChunk036AfterValue00 (fuel + 436) acc) :=
      congrArg (fun result => result.bind (simplicesChunk036AfterValue00 (fuel + 436) acc))
        (value_fragment161927 (fuel + 182) (simplicesChunk036SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 436) (SourceJson.white tail) (simplicesChunk036Push00 acc) := by rfl

noncomputable def simplicesArrayAcc03700 : List SourceJson := simplicesChunk036Push00 simplicesArrayAcc03600

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_036_generic_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_037_before_generic"
  err.flush

noncomputable def simplicesChunk037LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def simplicesChunk037SuffixChars00 : List Char := [',']
noncomputable def simplicesChunk037Chars00 : List Char := simplicesChunk037LeadChars00 ++ fragment163561Chars00 ++ simplicesChunk037SuffixChars00
noncomputable def simplicesChunk037Push00 (acc : List SourceJson) : List SourceJson := fragment163561Value00 :: acc

noncomputable def simplicesChunk037AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_simplices_chunk_037_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 436)
      (SourceJson.white (simplicesChunk037LeadChars00 ++ (fragment163561Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 435) (fragment163561Chars00 ++ rest)).bind
        (simplicesChunk037AfterValue00 (fuel + 435) acc) := by rfl

theorem array_simplices_chunk_037 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 436) (SourceJson.white (simplicesChunk037Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 435) (SourceJson.white tail) (simplicesChunk037Push00 acc) := by
  have hinput : simplicesChunk037Chars00 ++ tail = simplicesChunk037LeadChars00 ++ (fragment163561Chars00 ++ (simplicesChunk037SuffixChars00 ++ tail)) := by
    simp only [simplicesChunk037Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 436) (SourceJson.white (simplicesChunk037Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 436)
          (SourceJson.white (simplicesChunk037LeadChars00 ++ (fragment163561Chars00 ++ (simplicesChunk037SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 436) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 435) (fragment163561Chars00 ++ (simplicesChunk037SuffixChars00 ++ tail))).bind
        (simplicesChunk037AfterValue00 (fuel + 435) acc) := array_simplices_chunk_037_head fuel (simplicesChunk037SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment163561Value00, simplicesChunk037SuffixChars00 ++ tail)).bind
        (simplicesChunk037AfterValue00 (fuel + 435) acc) :=
      congrArg (fun result => result.bind (simplicesChunk037AfterValue00 (fuel + 435) acc))
        (value_fragment163561 (fuel + 205) (simplicesChunk037SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 435) (SourceJson.white tail) (simplicesChunk037Push00 acc) := by rfl

noncomputable def simplicesArrayAcc03800 : List SourceJson := simplicesChunk037Push00 simplicesArrayAcc03700

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_037_generic_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_038_before_generic"
  err.flush

noncomputable def simplicesChunk038LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def simplicesChunk038SuffixChars00 : List Char := [',']
noncomputable def simplicesChunk038Chars00 : List Char := simplicesChunk038LeadChars00 ++ fragment165148Chars00 ++ simplicesChunk038SuffixChars00
noncomputable def simplicesChunk038Push00 (acc : List SourceJson) : List SourceJson := fragment165148Value00 :: acc

noncomputable def simplicesChunk038AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_simplices_chunk_038_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 435)
      (SourceJson.white (simplicesChunk038LeadChars00 ++ (fragment165148Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 434) (fragment165148Chars00 ++ rest)).bind
        (simplicesChunk038AfterValue00 (fuel + 434) acc) := by rfl

theorem array_simplices_chunk_038 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 435) (SourceJson.white (simplicesChunk038Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 434) (SourceJson.white tail) (simplicesChunk038Push00 acc) := by
  have hinput : simplicesChunk038Chars00 ++ tail = simplicesChunk038LeadChars00 ++ (fragment165148Chars00 ++ (simplicesChunk038SuffixChars00 ++ tail)) := by
    simp only [simplicesChunk038Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 435) (SourceJson.white (simplicesChunk038Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 435)
          (SourceJson.white (simplicesChunk038LeadChars00 ++ (fragment165148Chars00 ++ (simplicesChunk038SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 435) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 434) (fragment165148Chars00 ++ (simplicesChunk038SuffixChars00 ++ tail))).bind
        (simplicesChunk038AfterValue00 (fuel + 434) acc) := array_simplices_chunk_038_head fuel (simplicesChunk038SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment165148Value00, simplicesChunk038SuffixChars00 ++ tail)).bind
        (simplicesChunk038AfterValue00 (fuel + 434) acc) :=
      congrArg (fun result => result.bind (simplicesChunk038AfterValue00 (fuel + 434) acc))
        (value_fragment165148 (fuel + 199) (simplicesChunk038SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 434) (SourceJson.white tail) (simplicesChunk038Push00 acc) := by rfl

noncomputable def simplicesArrayAcc03900 : List SourceJson := simplicesChunk038Push00 simplicesArrayAcc03800

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_038_generic_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_039_before_generic"
  err.flush

noncomputable def simplicesChunk039LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def simplicesChunk039SuffixChars00 : List Char := [',']
noncomputable def simplicesChunk039Chars00 : List Char := simplicesChunk039LeadChars00 ++ fragment166739Chars00 ++ simplicesChunk039SuffixChars00
noncomputable def simplicesChunk039Push00 (acc : List SourceJson) : List SourceJson := fragment166739Value00 :: acc

noncomputable def simplicesChunk039AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_simplices_chunk_039_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 434)
      (SourceJson.white (simplicesChunk039LeadChars00 ++ (fragment166739Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 433) (fragment166739Chars00 ++ rest)).bind
        (simplicesChunk039AfterValue00 (fuel + 433) acc) := by rfl

theorem array_simplices_chunk_039 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 434) (SourceJson.white (simplicesChunk039Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 433) (SourceJson.white tail) (simplicesChunk039Push00 acc) := by
  have hinput : simplicesChunk039Chars00 ++ tail = simplicesChunk039LeadChars00 ++ (fragment166739Chars00 ++ (simplicesChunk039SuffixChars00 ++ tail)) := by
    simp only [simplicesChunk039Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 434) (SourceJson.white (simplicesChunk039Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 434)
          (SourceJson.white (simplicesChunk039LeadChars00 ++ (fragment166739Chars00 ++ (simplicesChunk039SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 434) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 433) (fragment166739Chars00 ++ (simplicesChunk039SuffixChars00 ++ tail))).bind
        (simplicesChunk039AfterValue00 (fuel + 433) acc) := array_simplices_chunk_039_head fuel (simplicesChunk039SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment166739Value00, simplicesChunk039SuffixChars00 ++ tail)).bind
        (simplicesChunk039AfterValue00 (fuel + 433) acc) :=
      congrArg (fun result => result.bind (simplicesChunk039AfterValue00 (fuel + 433) acc))
        (value_fragment166739 (fuel + 196) (simplicesChunk039SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 433) (SourceJson.white tail) (simplicesChunk039Push00 acc) := by rfl

noncomputable def simplicesArrayAcc04000 : List SourceJson := simplicesChunk039Push00 simplicesArrayAcc03900

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_039_generic_complete"
  err.flush

noncomputable def simplicesBlock009Chars00 : List Char := simplicesChunk036Chars00 ++ simplicesChunk037Chars00 ++ simplicesChunk038Chars00 ++ simplicesChunk039Chars00
noncomputable def simplicesBlock009Push00 (acc : List SourceJson) : List SourceJson := simplicesChunk039Push00 (simplicesChunk038Push00 (simplicesChunk037Push00 (simplicesChunk036Push00 (acc))))

theorem array_simplices_block_009 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 437)
      (SourceJson.white (simplicesBlock009Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 433) (SourceJson.white tail) (simplicesBlock009Push00 acc) := by
  have hinput : simplicesBlock009Chars00 ++ tail = simplicesChunk036Chars00 ++ (simplicesChunk037Chars00 ++ (simplicesChunk038Chars00 ++ (simplicesChunk039Chars00 ++ (tail)))) := by
    simp only [simplicesBlock009Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 437)
        (SourceJson.white (simplicesBlock009Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 437) (SourceJson.white (simplicesChunk036Chars00 ++ (simplicesChunk037Chars00 ++ (simplicesChunk038Chars00 ++ (simplicesChunk039Chars00 ++ (tail)))))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 437) (SourceJson.white s) acc) hinput
    _ = SourceJson.array (fuel + 436) (SourceJson.white (simplicesChunk037Chars00 ++ (simplicesChunk038Chars00 ++ (simplicesChunk039Chars00 ++ (tail))))) (simplicesChunk036Push00 (acc)) := array_simplices_chunk_036 fuel (simplicesChunk037Chars00 ++ (simplicesChunk038Chars00 ++ (simplicesChunk039Chars00 ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 435) (SourceJson.white (simplicesChunk038Chars00 ++ (simplicesChunk039Chars00 ++ (tail)))) (simplicesChunk037Push00 (simplicesChunk036Push00 (acc))) := array_simplices_chunk_037 fuel (simplicesChunk038Chars00 ++ (simplicesChunk039Chars00 ++ (tail))) (simplicesChunk036Push00 (acc))
    _ = SourceJson.array (fuel + 434) (SourceJson.white (simplicesChunk039Chars00 ++ (tail))) (simplicesChunk038Push00 (simplicesChunk037Push00 (simplicesChunk036Push00 (acc)))) := array_simplices_chunk_038 fuel (simplicesChunk039Chars00 ++ (tail)) (simplicesChunk037Push00 (simplicesChunk036Push00 (acc)))
    _ = SourceJson.array (fuel + 433) (SourceJson.white tail) (simplicesBlock009Push00 acc) := array_simplices_chunk_039 fuel (tail) (simplicesChunk038Push00 (simplicesChunk037Push00 (simplicesChunk036Push00 (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_block_009_before_single_binding"
  err.flush

theorem geometryChars00_simplices_block_009_prefix :
    (geometryChars00.drop 161921).take 6393 = simplicesBlock009Chars00 := by rfl

theorem geometryChars00_simplices_block_009_split :
    geometryChars00.drop 161921 = simplicesBlock009Chars00 ++ geometryChars00.drop 168314 := by
  calc
    geometryChars00.drop 161921 =
        (geometryChars00.drop 161921).take 6393 ++ (geometryChars00.drop 161921).drop 6393 :=
      (List.take_append_drop 6393 (geometryChars00.drop 161921)).symm
    _ = simplicesBlock009Chars00 ++ (geometryChars00.drop 161921).drop 6393 :=
      congrArg (fun p => p ++ (geometryChars00.drop 161921).drop 6393) geometryChars00_simplices_block_009_prefix
    _ = simplicesBlock009Chars00 ++ geometryChars00.drop 168314 := by rw [List.drop_drop]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_block_009_after_single_binding"
  err.flush

theorem array_simplices_original_block_009 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 437)
      (SourceJson.white (geometryChars00.drop 161921)) acc =
      SourceJson.array (fuel + 433)
        (SourceJson.white (geometryChars00.drop 168314)) (simplicesBlock009Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 437) (SourceJson.white s) acc)
      geometryChars00_simplices_block_009_split).trans (array_simplices_block_009 fuel (geometryChars00.drop 168314) acc)

theorem simplices_array_through_block_009 (fuel : Nat) :
    SourceJson.array (fuel + 473)
      (SourceJson.white (geometryChars00.drop 100434)) [] =
      SourceJson.array (fuel + 433)
        (SourceJson.white (geometryChars00.drop 168314)) simplicesArrayAcc04000 := by
  exact (simplices_array_through_block_008 fuel).trans
    (array_simplices_original_block_009 fuel simplicesArrayAcc03600)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_block_009_complete"
  err.flush

#print axioms array_simplices_chunk_036_head
#print axioms array_simplices_chunk_036
#print axioms array_simplices_chunk_037_head
#print axioms array_simplices_chunk_037
#print axioms array_simplices_chunk_038_head
#print axioms array_simplices_chunk_038
#print axioms array_simplices_chunk_039_head
#print axioms array_simplices_chunk_039
#print axioms array_simplices_block_009
#print axioms geometryChars00_simplices_block_009_prefix
#print axioms geometryChars00_simplices_block_009_split
#print axioms array_simplices_original_block_009
#print axioms simplices_array_through_block_009

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
