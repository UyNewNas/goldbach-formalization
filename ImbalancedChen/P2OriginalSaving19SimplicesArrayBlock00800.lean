import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00700
import ImbalancedChen.P2OriginalSaving19ValueFragment15539900
import ImbalancedChen.P2OriginalSaving19ValueFragment15699000
import ImbalancedChen.P2OriginalSaving19ValueFragment15857000
import ImbalancedChen.P2OriginalSaving19ValueFragment16006800

/-! Original simplices block 8/13. Generic small chunks are composed first; exact original bytes are then bound once for the complete block, retaining the original arbitrary tail and accumulator semantics.
Exact original bytes are candidate data; the original reader equations below
are the Lean checks. No whole-file decide or replacement reader is used. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_032_before_generic"
  err.flush

noncomputable def simplicesChunk032LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def simplicesChunk032SuffixChars00 : List Char := [',']
noncomputable def simplicesChunk032Chars00 : List Char := simplicesChunk032LeadChars00 ++ fragment155399Chars00 ++ simplicesChunk032SuffixChars00
noncomputable def simplicesChunk032Push00 (acc : List SourceJson) : List SourceJson := fragment155399Value00 :: acc

noncomputable def simplicesChunk032AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_simplices_chunk_032_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 441)
      (SourceJson.white (simplicesChunk032LeadChars00 ++ (fragment155399Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 440) (fragment155399Chars00 ++ rest)).bind
        (simplicesChunk032AfterValue00 (fuel + 440) acc) := by rfl

theorem array_simplices_chunk_032 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 441) (SourceJson.white (simplicesChunk032Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 440) (SourceJson.white tail) (simplicesChunk032Push00 acc) := by
  have hinput : simplicesChunk032Chars00 ++ tail = simplicesChunk032LeadChars00 ++ (fragment155399Chars00 ++ (simplicesChunk032SuffixChars00 ++ tail)) := by
    simp only [simplicesChunk032Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 441) (SourceJson.white (simplicesChunk032Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 441)
          (SourceJson.white (simplicesChunk032LeadChars00 ++ (fragment155399Chars00 ++ (simplicesChunk032SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 441) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 440) (fragment155399Chars00 ++ (simplicesChunk032SuffixChars00 ++ tail))).bind
        (simplicesChunk032AfterValue00 (fuel + 440) acc) := array_simplices_chunk_032_head fuel (simplicesChunk032SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment155399Value00, simplicesChunk032SuffixChars00 ++ tail)).bind
        (simplicesChunk032AfterValue00 (fuel + 440) acc) :=
      congrArg (fun result => result.bind (simplicesChunk032AfterValue00 (fuel + 440) acc))
        (value_fragment155399 (fuel + 206) (simplicesChunk032SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 440) (SourceJson.white tail) (simplicesChunk032Push00 acc) := by rfl

noncomputable def simplicesArrayAcc03300 : List SourceJson := simplicesChunk032Push00 simplicesArrayAcc03200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_032_generic_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_033_before_generic"
  err.flush

noncomputable def simplicesChunk033LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def simplicesChunk033SuffixChars00 : List Char := [',']
noncomputable def simplicesChunk033Chars00 : List Char := simplicesChunk033LeadChars00 ++ fragment156990Chars00 ++ simplicesChunk033SuffixChars00
noncomputable def simplicesChunk033Push00 (acc : List SourceJson) : List SourceJson := fragment156990Value00 :: acc

noncomputable def simplicesChunk033AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_simplices_chunk_033_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 440)
      (SourceJson.white (simplicesChunk033LeadChars00 ++ (fragment156990Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 439) (fragment156990Chars00 ++ rest)).bind
        (simplicesChunk033AfterValue00 (fuel + 439) acc) := by rfl

theorem array_simplices_chunk_033 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 440) (SourceJson.white (simplicesChunk033Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 439) (SourceJson.white tail) (simplicesChunk033Push00 acc) := by
  have hinput : simplicesChunk033Chars00 ++ tail = simplicesChunk033LeadChars00 ++ (fragment156990Chars00 ++ (simplicesChunk033SuffixChars00 ++ tail)) := by
    simp only [simplicesChunk033Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 440) (SourceJson.white (simplicesChunk033Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 440)
          (SourceJson.white (simplicesChunk033LeadChars00 ++ (fragment156990Chars00 ++ (simplicesChunk033SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 440) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 439) (fragment156990Chars00 ++ (simplicesChunk033SuffixChars00 ++ tail))).bind
        (simplicesChunk033AfterValue00 (fuel + 439) acc) := array_simplices_chunk_033_head fuel (simplicesChunk033SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment156990Value00, simplicesChunk033SuffixChars00 ++ tail)).bind
        (simplicesChunk033AfterValue00 (fuel + 439) acc) :=
      congrArg (fun result => result.bind (simplicesChunk033AfterValue00 (fuel + 439) acc))
        (value_fragment156990 (fuel + 202) (simplicesChunk033SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 439) (SourceJson.white tail) (simplicesChunk033Push00 acc) := by rfl

noncomputable def simplicesArrayAcc03400 : List SourceJson := simplicesChunk033Push00 simplicesArrayAcc03300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_033_generic_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_034_before_generic"
  err.flush

noncomputable def simplicesChunk034LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def simplicesChunk034SuffixChars00 : List Char := [',']
noncomputable def simplicesChunk034Chars00 : List Char := simplicesChunk034LeadChars00 ++ fragment158570Chars00 ++ simplicesChunk034SuffixChars00
noncomputable def simplicesChunk034Push00 (acc : List SourceJson) : List SourceJson := fragment158570Value00 :: acc

noncomputable def simplicesChunk034AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_simplices_chunk_034_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 439)
      (SourceJson.white (simplicesChunk034LeadChars00 ++ (fragment158570Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 438) (fragment158570Chars00 ++ rest)).bind
        (simplicesChunk034AfterValue00 (fuel + 438) acc) := by rfl

theorem array_simplices_chunk_034 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 439) (SourceJson.white (simplicesChunk034Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 438) (SourceJson.white tail) (simplicesChunk034Push00 acc) := by
  have hinput : simplicesChunk034Chars00 ++ tail = simplicesChunk034LeadChars00 ++ (fragment158570Chars00 ++ (simplicesChunk034SuffixChars00 ++ tail)) := by
    simp only [simplicesChunk034Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 439) (SourceJson.white (simplicesChunk034Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 439)
          (SourceJson.white (simplicesChunk034LeadChars00 ++ (fragment158570Chars00 ++ (simplicesChunk034SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 439) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 438) (fragment158570Chars00 ++ (simplicesChunk034SuffixChars00 ++ tail))).bind
        (simplicesChunk034AfterValue00 (fuel + 438) acc) := array_simplices_chunk_034_head fuel (simplicesChunk034SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment158570Value00, simplicesChunk034SuffixChars00 ++ tail)).bind
        (simplicesChunk034AfterValue00 (fuel + 438) acc) :=
      congrArg (fun result => result.bind (simplicesChunk034AfterValue00 (fuel + 438) acc))
        (value_fragment158570 (fuel + 243) (simplicesChunk034SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 438) (SourceJson.white tail) (simplicesChunk034Push00 acc) := by rfl

noncomputable def simplicesArrayAcc03500 : List SourceJson := simplicesChunk034Push00 simplicesArrayAcc03400

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_034_generic_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_035_before_generic"
  err.flush

noncomputable def simplicesChunk035LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def simplicesChunk035SuffixChars00 : List Char := [',']
noncomputable def simplicesChunk035Chars00 : List Char := simplicesChunk035LeadChars00 ++ fragment160068Chars00 ++ simplicesChunk035SuffixChars00
noncomputable def simplicesChunk035Push00 (acc : List SourceJson) : List SourceJson := fragment160068Value00 :: acc

noncomputable def simplicesChunk035AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_simplices_chunk_035_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 438)
      (SourceJson.white (simplicesChunk035LeadChars00 ++ (fragment160068Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 437) (fragment160068Chars00 ++ rest)).bind
        (simplicesChunk035AfterValue00 (fuel + 437) acc) := by rfl

theorem array_simplices_chunk_035 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 438) (SourceJson.white (simplicesChunk035Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 437) (SourceJson.white tail) (simplicesChunk035Push00 acc) := by
  have hinput : simplicesChunk035Chars00 ++ tail = simplicesChunk035LeadChars00 ++ (fragment160068Chars00 ++ (simplicesChunk035SuffixChars00 ++ tail)) := by
    simp only [simplicesChunk035Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 438) (SourceJson.white (simplicesChunk035Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 438)
          (SourceJson.white (simplicesChunk035LeadChars00 ++ (fragment160068Chars00 ++ (simplicesChunk035SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 438) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 437) (fragment160068Chars00 ++ (simplicesChunk035SuffixChars00 ++ tail))).bind
        (simplicesChunk035AfterValue00 (fuel + 437) acc) := array_simplices_chunk_035_head fuel (simplicesChunk035SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment160068Value00, simplicesChunk035SuffixChars00 ++ tail)).bind
        (simplicesChunk035AfterValue00 (fuel + 437) acc) :=
      congrArg (fun result => result.bind (simplicesChunk035AfterValue00 (fuel + 437) acc))
        (value_fragment160068 (fuel + 73) (simplicesChunk035SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 437) (SourceJson.white tail) (simplicesChunk035Push00 acc) := by rfl

noncomputable def simplicesArrayAcc03600 : List SourceJson := simplicesChunk035Push00 simplicesArrayAcc03500

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_035_generic_complete"
  err.flush

noncomputable def simplicesBlock008Chars00 : List Char := simplicesChunk032Chars00 ++ simplicesChunk033Chars00 ++ simplicesChunk034Chars00 ++ simplicesChunk035Chars00
noncomputable def simplicesBlock008Push00 (acc : List SourceJson) : List SourceJson := simplicesChunk035Push00 (simplicesChunk034Push00 (simplicesChunk033Push00 (simplicesChunk032Push00 (acc))))

theorem array_simplices_block_008 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 441)
      (SourceJson.white (simplicesBlock008Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 437) (SourceJson.white tail) (simplicesBlock008Push00 acc) := by
  have hinput : simplicesBlock008Chars00 ++ tail = simplicesChunk032Chars00 ++ (simplicesChunk033Chars00 ++ (simplicesChunk034Chars00 ++ (simplicesChunk035Chars00 ++ (tail)))) := by
    simp only [simplicesBlock008Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 441)
        (SourceJson.white (simplicesBlock008Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 441) (SourceJson.white (simplicesChunk032Chars00 ++ (simplicesChunk033Chars00 ++ (simplicesChunk034Chars00 ++ (simplicesChunk035Chars00 ++ (tail)))))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 441) (SourceJson.white s) acc) hinput
    _ = SourceJson.array (fuel + 440) (SourceJson.white (simplicesChunk033Chars00 ++ (simplicesChunk034Chars00 ++ (simplicesChunk035Chars00 ++ (tail))))) (simplicesChunk032Push00 (acc)) := array_simplices_chunk_032 fuel (simplicesChunk033Chars00 ++ (simplicesChunk034Chars00 ++ (simplicesChunk035Chars00 ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 439) (SourceJson.white (simplicesChunk034Chars00 ++ (simplicesChunk035Chars00 ++ (tail)))) (simplicesChunk033Push00 (simplicesChunk032Push00 (acc))) := array_simplices_chunk_033 fuel (simplicesChunk034Chars00 ++ (simplicesChunk035Chars00 ++ (tail))) (simplicesChunk032Push00 (acc))
    _ = SourceJson.array (fuel + 438) (SourceJson.white (simplicesChunk035Chars00 ++ (tail))) (simplicesChunk034Push00 (simplicesChunk033Push00 (simplicesChunk032Push00 (acc)))) := array_simplices_chunk_034 fuel (simplicesChunk035Chars00 ++ (tail)) (simplicesChunk033Push00 (simplicesChunk032Push00 (acc)))
    _ = SourceJson.array (fuel + 437) (SourceJson.white tail) (simplicesBlock008Push00 acc) := array_simplices_chunk_035 fuel (tail) (simplicesChunk034Push00 (simplicesChunk033Push00 (simplicesChunk032Push00 (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_block_008_before_single_binding"
  err.flush

theorem geometryChars00_simplices_block_008_prefix :
    (geometryChars00.drop 155393).take 6528 = simplicesBlock008Chars00 := by rfl

theorem geometryChars00_simplices_block_008_split :
    geometryChars00.drop 155393 = simplicesBlock008Chars00 ++ geometryChars00.drop 161921 := by
  calc
    geometryChars00.drop 155393 =
        (geometryChars00.drop 155393).take 6528 ++ (geometryChars00.drop 155393).drop 6528 :=
      (List.take_append_drop 6528 (geometryChars00.drop 155393)).symm
    _ = simplicesBlock008Chars00 ++ (geometryChars00.drop 155393).drop 6528 :=
      congrArg (fun p => p ++ (geometryChars00.drop 155393).drop 6528) geometryChars00_simplices_block_008_prefix
    _ = simplicesBlock008Chars00 ++ geometryChars00.drop 161921 := by rw [List.drop_drop]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_block_008_after_single_binding"
  err.flush

theorem array_simplices_original_block_008 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 441)
      (SourceJson.white (geometryChars00.drop 155393)) acc =
      SourceJson.array (fuel + 437)
        (SourceJson.white (geometryChars00.drop 161921)) (simplicesBlock008Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 441) (SourceJson.white s) acc)
      geometryChars00_simplices_block_008_split).trans (array_simplices_block_008 fuel (geometryChars00.drop 161921) acc)

theorem simplices_array_through_block_008 (fuel : Nat) :
    SourceJson.array (fuel + 473)
      (SourceJson.white (geometryChars00.drop 100434)) [] =
      SourceJson.array (fuel + 437)
        (SourceJson.white (geometryChars00.drop 161921)) simplicesArrayAcc03600 := by
  exact (simplices_array_through_block_007 fuel).trans
    (array_simplices_original_block_008 fuel simplicesArrayAcc03200)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_block_008_complete"
  err.flush

#print axioms array_simplices_chunk_032_head
#print axioms array_simplices_chunk_032
#print axioms array_simplices_chunk_033_head
#print axioms array_simplices_chunk_033
#print axioms array_simplices_chunk_034_head
#print axioms array_simplices_chunk_034
#print axioms array_simplices_chunk_035_head
#print axioms array_simplices_chunk_035
#print axioms array_simplices_block_008
#print axioms geometryChars00_simplices_block_008_prefix
#print axioms geometryChars00_simplices_block_008_split
#print axioms array_simplices_original_block_008
#print axioms simplices_array_through_block_008

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
