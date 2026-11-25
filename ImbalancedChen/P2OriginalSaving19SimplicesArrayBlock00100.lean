import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00000
import ImbalancedChen.P2OriginalSaving19ValueFragment10737400
import ImbalancedChen.P2OriginalSaving19ValueFragment10904400
import ImbalancedChen.P2OriginalSaving19ValueFragment11065200
import ImbalancedChen.P2OriginalSaving19ValueFragment11222800

/-! Original simplices block 1/13. Generic small chunks are composed first; exact original bytes are then bound once for the complete block, retaining the original arbitrary tail and accumulator semantics.
Exact original bytes are candidate data; the original reader equations below
are the Lean checks. No whole-file decide or replacement reader is used. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_004_before_generic"
  err.flush

noncomputable def simplicesChunk004LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def simplicesChunk004SuffixChars00 : List Char := [',']
noncomputable def simplicesChunk004Chars00 : List Char := simplicesChunk004LeadChars00 ++ fragment107374Chars00 ++ simplicesChunk004SuffixChars00
noncomputable def simplicesChunk004Push00 (acc : List SourceJson) : List SourceJson := fragment107374Value00 :: acc

noncomputable def simplicesChunk004AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_simplices_chunk_004_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 469)
      (SourceJson.white (simplicesChunk004LeadChars00 ++ (fragment107374Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 468) (fragment107374Chars00 ++ rest)).bind
        (simplicesChunk004AfterValue00 (fuel + 468) acc) := by rfl

theorem array_simplices_chunk_004 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 469) (SourceJson.white (simplicesChunk004Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 468) (SourceJson.white tail) (simplicesChunk004Push00 acc) := by
  have hinput : simplicesChunk004Chars00 ++ tail = simplicesChunk004LeadChars00 ++ (fragment107374Chars00 ++ (simplicesChunk004SuffixChars00 ++ tail)) := by
    simp only [simplicesChunk004Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 469) (SourceJson.white (simplicesChunk004Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 469)
          (SourceJson.white (simplicesChunk004LeadChars00 ++ (fragment107374Chars00 ++ (simplicesChunk004SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 469) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 468) (fragment107374Chars00 ++ (simplicesChunk004SuffixChars00 ++ tail))).bind
        (simplicesChunk004AfterValue00 (fuel + 468) acc) := array_simplices_chunk_004_head fuel (simplicesChunk004SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment107374Value00, simplicesChunk004SuffixChars00 ++ tail)).bind
        (simplicesChunk004AfterValue00 (fuel + 468) acc) :=
      congrArg (fun result => result.bind (simplicesChunk004AfterValue00 (fuel + 468) acc))
        (value_fragment107374 (fuel + 210) (simplicesChunk004SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 468) (SourceJson.white tail) (simplicesChunk004Push00 acc) := by rfl

noncomputable def simplicesArrayAcc00500 : List SourceJson := simplicesChunk004Push00 simplicesArrayAcc00400

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_004_generic_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_005_before_generic"
  err.flush

noncomputable def simplicesChunk005LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def simplicesChunk005SuffixChars00 : List Char := [',']
noncomputable def simplicesChunk005Chars00 : List Char := simplicesChunk005LeadChars00 ++ fragment109044Chars00 ++ simplicesChunk005SuffixChars00
noncomputable def simplicesChunk005Push00 (acc : List SourceJson) : List SourceJson := fragment109044Value00 :: acc

noncomputable def simplicesChunk005AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_simplices_chunk_005_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 468)
      (SourceJson.white (simplicesChunk005LeadChars00 ++ (fragment109044Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 467) (fragment109044Chars00 ++ rest)).bind
        (simplicesChunk005AfterValue00 (fuel + 467) acc) := by rfl

theorem array_simplices_chunk_005 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 468) (SourceJson.white (simplicesChunk005Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 467) (SourceJson.white tail) (simplicesChunk005Push00 acc) := by
  have hinput : simplicesChunk005Chars00 ++ tail = simplicesChunk005LeadChars00 ++ (fragment109044Chars00 ++ (simplicesChunk005SuffixChars00 ++ tail)) := by
    simp only [simplicesChunk005Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 468) (SourceJson.white (simplicesChunk005Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 468)
          (SourceJson.white (simplicesChunk005LeadChars00 ++ (fragment109044Chars00 ++ (simplicesChunk005SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 468) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 467) (fragment109044Chars00 ++ (simplicesChunk005SuffixChars00 ++ tail))).bind
        (simplicesChunk005AfterValue00 (fuel + 467) acc) := array_simplices_chunk_005_head fuel (simplicesChunk005SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment109044Value00, simplicesChunk005SuffixChars00 ++ tail)).bind
        (simplicesChunk005AfterValue00 (fuel + 467) acc) :=
      congrArg (fun result => result.bind (simplicesChunk005AfterValue00 (fuel + 467) acc))
        (value_fragment109044 (fuel + 224) (simplicesChunk005SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 467) (SourceJson.white tail) (simplicesChunk005Push00 acc) := by rfl

noncomputable def simplicesArrayAcc00600 : List SourceJson := simplicesChunk005Push00 simplicesArrayAcc00500

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_005_generic_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_006_before_generic"
  err.flush

noncomputable def simplicesChunk006LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def simplicesChunk006SuffixChars00 : List Char := [',']
noncomputable def simplicesChunk006Chars00 : List Char := simplicesChunk006LeadChars00 ++ fragment110652Chars00 ++ simplicesChunk006SuffixChars00
noncomputable def simplicesChunk006Push00 (acc : List SourceJson) : List SourceJson := fragment110652Value00 :: acc

noncomputable def simplicesChunk006AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_simplices_chunk_006_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 467)
      (SourceJson.white (simplicesChunk006LeadChars00 ++ (fragment110652Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 466) (fragment110652Chars00 ++ rest)).bind
        (simplicesChunk006AfterValue00 (fuel + 466) acc) := by rfl

theorem array_simplices_chunk_006 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 467) (SourceJson.white (simplicesChunk006Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 466) (SourceJson.white tail) (simplicesChunk006Push00 acc) := by
  have hinput : simplicesChunk006Chars00 ++ tail = simplicesChunk006LeadChars00 ++ (fragment110652Chars00 ++ (simplicesChunk006SuffixChars00 ++ tail)) := by
    simp only [simplicesChunk006Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 467) (SourceJson.white (simplicesChunk006Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 467)
          (SourceJson.white (simplicesChunk006LeadChars00 ++ (fragment110652Chars00 ++ (simplicesChunk006SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 467) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 466) (fragment110652Chars00 ++ (simplicesChunk006SuffixChars00 ++ tail))).bind
        (simplicesChunk006AfterValue00 (fuel + 466) acc) := array_simplices_chunk_006_head fuel (simplicesChunk006SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment110652Value00, simplicesChunk006SuffixChars00 ++ tail)).bind
        (simplicesChunk006AfterValue00 (fuel + 466) acc) :=
      congrArg (fun result => result.bind (simplicesChunk006AfterValue00 (fuel + 466) acc))
        (value_fragment110652 (fuel + 242) (simplicesChunk006SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 466) (SourceJson.white tail) (simplicesChunk006Push00 acc) := by rfl

noncomputable def simplicesArrayAcc00700 : List SourceJson := simplicesChunk006Push00 simplicesArrayAcc00600

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_006_generic_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_007_before_generic"
  err.flush

noncomputable def simplicesChunk007LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def simplicesChunk007SuffixChars00 : List Char := [',']
noncomputable def simplicesChunk007Chars00 : List Char := simplicesChunk007LeadChars00 ++ fragment112228Chars00 ++ simplicesChunk007SuffixChars00
noncomputable def simplicesChunk007Push00 (acc : List SourceJson) : List SourceJson := fragment112228Value00 :: acc

noncomputable def simplicesChunk007AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_simplices_chunk_007_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 466)
      (SourceJson.white (simplicesChunk007LeadChars00 ++ (fragment112228Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 465) (fragment112228Chars00 ++ rest)).bind
        (simplicesChunk007AfterValue00 (fuel + 465) acc) := by rfl

theorem array_simplices_chunk_007 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 466) (SourceJson.white (simplicesChunk007Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 465) (SourceJson.white tail) (simplicesChunk007Push00 acc) := by
  have hinput : simplicesChunk007Chars00 ++ tail = simplicesChunk007LeadChars00 ++ (fragment112228Chars00 ++ (simplicesChunk007SuffixChars00 ++ tail)) := by
    simp only [simplicesChunk007Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 466) (SourceJson.white (simplicesChunk007Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 466)
          (SourceJson.white (simplicesChunk007LeadChars00 ++ (fragment112228Chars00 ++ (simplicesChunk007SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 466) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 465) (fragment112228Chars00 ++ (simplicesChunk007SuffixChars00 ++ tail))).bind
        (simplicesChunk007AfterValue00 (fuel + 465) acc) := array_simplices_chunk_007_head fuel (simplicesChunk007SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment112228Value00, simplicesChunk007SuffixChars00 ++ tail)).bind
        (simplicesChunk007AfterValue00 (fuel + 465) acc) :=
      congrArg (fun result => result.bind (simplicesChunk007AfterValue00 (fuel + 465) acc))
        (value_fragment112228 (fuel + 61) (simplicesChunk007SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 465) (SourceJson.white tail) (simplicesChunk007Push00 acc) := by rfl

noncomputable def simplicesArrayAcc00800 : List SourceJson := simplicesChunk007Push00 simplicesArrayAcc00700

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_007_generic_complete"
  err.flush

noncomputable def simplicesBlock001Chars00 : List Char := simplicesChunk004Chars00 ++ simplicesChunk005Chars00 ++ simplicesChunk006Chars00 ++ simplicesChunk007Chars00
noncomputable def simplicesBlock001Push00 (acc : List SourceJson) : List SourceJson := simplicesChunk007Push00 (simplicesChunk006Push00 (simplicesChunk005Push00 (simplicesChunk004Push00 (acc))))

theorem array_simplices_block_001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 469)
      (SourceJson.white (simplicesBlock001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 465) (SourceJson.white tail) (simplicesBlock001Push00 acc) := by
  have hinput : simplicesBlock001Chars00 ++ tail = simplicesChunk004Chars00 ++ (simplicesChunk005Chars00 ++ (simplicesChunk006Chars00 ++ (simplicesChunk007Chars00 ++ (tail)))) := by
    simp only [simplicesBlock001Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 469)
        (SourceJson.white (simplicesBlock001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 469) (SourceJson.white (simplicesChunk004Chars00 ++ (simplicesChunk005Chars00 ++ (simplicesChunk006Chars00 ++ (simplicesChunk007Chars00 ++ (tail)))))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 469) (SourceJson.white s) acc) hinput
    _ = SourceJson.array (fuel + 468) (SourceJson.white (simplicesChunk005Chars00 ++ (simplicesChunk006Chars00 ++ (simplicesChunk007Chars00 ++ (tail))))) (simplicesChunk004Push00 (acc)) := array_simplices_chunk_004 fuel (simplicesChunk005Chars00 ++ (simplicesChunk006Chars00 ++ (simplicesChunk007Chars00 ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 467) (SourceJson.white (simplicesChunk006Chars00 ++ (simplicesChunk007Chars00 ++ (tail)))) (simplicesChunk005Push00 (simplicesChunk004Push00 (acc))) := array_simplices_chunk_005 fuel (simplicesChunk006Chars00 ++ (simplicesChunk007Chars00 ++ (tail))) (simplicesChunk004Push00 (acc))
    _ = SourceJson.array (fuel + 466) (SourceJson.white (simplicesChunk007Chars00 ++ (tail))) (simplicesChunk006Push00 (simplicesChunk005Push00 (simplicesChunk004Push00 (acc)))) := array_simplices_chunk_006 fuel (simplicesChunk007Chars00 ++ (tail)) (simplicesChunk005Push00 (simplicesChunk004Push00 (acc)))
    _ = SourceJson.array (fuel + 465) (SourceJson.white tail) (simplicesBlock001Push00 acc) := array_simplices_chunk_007 fuel (tail) (simplicesChunk006Push00 (simplicesChunk005Push00 (simplicesChunk004Push00 (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_block_001_before_single_binding"
  err.flush

theorem geometryChars00_simplices_block_001_prefix :
    (geometryChars00.drop 107368).take 6817 = simplicesBlock001Chars00 := by rfl

theorem geometryChars00_simplices_block_001_split :
    geometryChars00.drop 107368 = simplicesBlock001Chars00 ++ geometryChars00.drop 114185 := by
  calc
    geometryChars00.drop 107368 =
        (geometryChars00.drop 107368).take 6817 ++ (geometryChars00.drop 107368).drop 6817 :=
      (List.take_append_drop 6817 (geometryChars00.drop 107368)).symm
    _ = simplicesBlock001Chars00 ++ (geometryChars00.drop 107368).drop 6817 :=
      congrArg (fun p => p ++ (geometryChars00.drop 107368).drop 6817) geometryChars00_simplices_block_001_prefix
    _ = simplicesBlock001Chars00 ++ geometryChars00.drop 114185 := by rw [List.drop_drop]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_block_001_after_single_binding"
  err.flush

theorem array_simplices_original_block_001 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 469)
      (SourceJson.white (geometryChars00.drop 107368)) acc =
      SourceJson.array (fuel + 465)
        (SourceJson.white (geometryChars00.drop 114185)) (simplicesBlock001Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 469) (SourceJson.white s) acc)
      geometryChars00_simplices_block_001_split).trans (array_simplices_block_001 fuel (geometryChars00.drop 114185) acc)

theorem simplices_array_through_block_001 (fuel : Nat) :
    SourceJson.array (fuel + 473)
      (SourceJson.white (geometryChars00.drop 100434)) [] =
      SourceJson.array (fuel + 465)
        (SourceJson.white (geometryChars00.drop 114185)) simplicesArrayAcc00800 := by
  exact (simplices_array_through_block_000 fuel).trans
    (array_simplices_original_block_001 fuel simplicesArrayAcc00400)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_block_001_complete"
  err.flush

#print axioms array_simplices_chunk_004_head
#print axioms array_simplices_chunk_004
#print axioms array_simplices_chunk_005_head
#print axioms array_simplices_chunk_005
#print axioms array_simplices_chunk_006_head
#print axioms array_simplices_chunk_006
#print axioms array_simplices_chunk_007_head
#print axioms array_simplices_chunk_007
#print axioms array_simplices_block_001
#print axioms geometryChars00_simplices_block_001_prefix
#print axioms geometryChars00_simplices_block_001_split
#print axioms array_simplices_original_block_001
#print axioms simplices_array_through_block_001

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
