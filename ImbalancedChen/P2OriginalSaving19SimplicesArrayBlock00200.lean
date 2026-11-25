import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00100
import ImbalancedChen.P2OriginalSaving19ValueFragment11419100
import ImbalancedChen.P2OriginalSaving19ValueFragment11588600
import ImbalancedChen.P2OriginalSaving19ValueFragment11748100
import ImbalancedChen.P2OriginalSaving19ValueFragment11910300

/-! Original simplices block 2/13. Generic small chunks are composed first; exact original bytes are then bound once for the complete block, retaining the original arbitrary tail and accumulator semantics.
Exact original bytes are candidate data; the original reader equations below
are the Lean checks. No whole-file decide or replacement reader is used. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_008_before_generic"
  err.flush

noncomputable def simplicesChunk008LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def simplicesChunk008SuffixChars00 : List Char := [',']
noncomputable def simplicesChunk008Chars00 : List Char := simplicesChunk008LeadChars00 ++ fragment114191Chars00 ++ simplicesChunk008SuffixChars00
noncomputable def simplicesChunk008Push00 (acc : List SourceJson) : List SourceJson := fragment114191Value00 :: acc

noncomputable def simplicesChunk008AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_simplices_chunk_008_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 465)
      (SourceJson.white (simplicesChunk008LeadChars00 ++ (fragment114191Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 464) (fragment114191Chars00 ++ rest)).bind
        (simplicesChunk008AfterValue00 (fuel + 464) acc) := by rfl

theorem array_simplices_chunk_008 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 465) (SourceJson.white (simplicesChunk008Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 464) (SourceJson.white tail) (simplicesChunk008Push00 acc) := by
  have hinput : simplicesChunk008Chars00 ++ tail = simplicesChunk008LeadChars00 ++ (fragment114191Chars00 ++ (simplicesChunk008SuffixChars00 ++ tail)) := by
    simp only [simplicesChunk008Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 465) (SourceJson.white (simplicesChunk008Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 465)
          (SourceJson.white (simplicesChunk008LeadChars00 ++ (fragment114191Chars00 ++ (simplicesChunk008SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 465) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 464) (fragment114191Chars00 ++ (simplicesChunk008SuffixChars00 ++ tail))).bind
        (simplicesChunk008AfterValue00 (fuel + 464) acc) := array_simplices_chunk_008_head fuel (simplicesChunk008SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment114191Value00, simplicesChunk008SuffixChars00 ++ tail)).bind
        (simplicesChunk008AfterValue00 (fuel + 464) acc) :=
      congrArg (fun result => result.bind (simplicesChunk008AfterValue00 (fuel + 464) acc))
        (value_fragment114191 (fuel + 190) (simplicesChunk008SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 464) (SourceJson.white tail) (simplicesChunk008Push00 acc) := by rfl

noncomputable def simplicesArrayAcc00900 : List SourceJson := simplicesChunk008Push00 simplicesArrayAcc00800

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_008_generic_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_009_before_generic"
  err.flush

noncomputable def simplicesChunk009LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def simplicesChunk009SuffixChars00 : List Char := [',']
noncomputable def simplicesChunk009Chars00 : List Char := simplicesChunk009LeadChars00 ++ fragment115886Chars00 ++ simplicesChunk009SuffixChars00
noncomputable def simplicesChunk009Push00 (acc : List SourceJson) : List SourceJson := fragment115886Value00 :: acc

noncomputable def simplicesChunk009AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_simplices_chunk_009_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 464)
      (SourceJson.white (simplicesChunk009LeadChars00 ++ (fragment115886Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 463) (fragment115886Chars00 ++ rest)).bind
        (simplicesChunk009AfterValue00 (fuel + 463) acc) := by rfl

theorem array_simplices_chunk_009 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 464) (SourceJson.white (simplicesChunk009Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 463) (SourceJson.white tail) (simplicesChunk009Push00 acc) := by
  have hinput : simplicesChunk009Chars00 ++ tail = simplicesChunk009LeadChars00 ++ (fragment115886Chars00 ++ (simplicesChunk009SuffixChars00 ++ tail)) := by
    simp only [simplicesChunk009Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 464) (SourceJson.white (simplicesChunk009Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 464)
          (SourceJson.white (simplicesChunk009LeadChars00 ++ (fragment115886Chars00 ++ (simplicesChunk009SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 464) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 463) (fragment115886Chars00 ++ (simplicesChunk009SuffixChars00 ++ tail))).bind
        (simplicesChunk009AfterValue00 (fuel + 463) acc) := array_simplices_chunk_009_head fuel (simplicesChunk009SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment115886Value00, simplicesChunk009SuffixChars00 ++ tail)).bind
        (simplicesChunk009AfterValue00 (fuel + 463) acc) :=
      congrArg (fun result => result.bind (simplicesChunk009AfterValue00 (fuel + 463) acc))
        (value_fragment115886 (fuel + 227) (simplicesChunk009SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 463) (SourceJson.white tail) (simplicesChunk009Push00 acc) := by rfl

noncomputable def simplicesArrayAcc01000 : List SourceJson := simplicesChunk009Push00 simplicesArrayAcc00900

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_009_generic_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_010_before_generic"
  err.flush

noncomputable def simplicesChunk010LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def simplicesChunk010SuffixChars00 : List Char := [',']
noncomputable def simplicesChunk010Chars00 : List Char := simplicesChunk010LeadChars00 ++ fragment117481Chars00 ++ simplicesChunk010SuffixChars00
noncomputable def simplicesChunk010Push00 (acc : List SourceJson) : List SourceJson := fragment117481Value00 :: acc

noncomputable def simplicesChunk010AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_simplices_chunk_010_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 463)
      (SourceJson.white (simplicesChunk010LeadChars00 ++ (fragment117481Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 462) (fragment117481Chars00 ++ rest)).bind
        (simplicesChunk010AfterValue00 (fuel + 462) acc) := by rfl

theorem array_simplices_chunk_010 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 463) (SourceJson.white (simplicesChunk010Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 462) (SourceJson.white tail) (simplicesChunk010Push00 acc) := by
  have hinput : simplicesChunk010Chars00 ++ tail = simplicesChunk010LeadChars00 ++ (fragment117481Chars00 ++ (simplicesChunk010SuffixChars00 ++ tail)) := by
    simp only [simplicesChunk010Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 463) (SourceJson.white (simplicesChunk010Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 463)
          (SourceJson.white (simplicesChunk010LeadChars00 ++ (fragment117481Chars00 ++ (simplicesChunk010SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 463) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 462) (fragment117481Chars00 ++ (simplicesChunk010SuffixChars00 ++ tail))).bind
        (simplicesChunk010AfterValue00 (fuel + 462) acc) := array_simplices_chunk_010_head fuel (simplicesChunk010SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment117481Value00, simplicesChunk010SuffixChars00 ++ tail)).bind
        (simplicesChunk010AfterValue00 (fuel + 462) acc) :=
      congrArg (fun result => result.bind (simplicesChunk010AfterValue00 (fuel + 462) acc))
        (value_fragment117481 (fuel + 222) (simplicesChunk010SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 462) (SourceJson.white tail) (simplicesChunk010Push00 acc) := by rfl

noncomputable def simplicesArrayAcc01100 : List SourceJson := simplicesChunk010Push00 simplicesArrayAcc01000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_010_generic_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_011_before_generic"
  err.flush

noncomputable def simplicesChunk011LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def simplicesChunk011SuffixChars00 : List Char := [',']
noncomputable def simplicesChunk011Chars00 : List Char := simplicesChunk011LeadChars00 ++ fragment119103Chars00 ++ simplicesChunk011SuffixChars00
noncomputable def simplicesChunk011Push00 (acc : List SourceJson) : List SourceJson := fragment119103Value00 :: acc

noncomputable def simplicesChunk011AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_simplices_chunk_011_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 462)
      (SourceJson.white (simplicesChunk011LeadChars00 ++ (fragment119103Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 461) (fragment119103Chars00 ++ rest)).bind
        (simplicesChunk011AfterValue00 (fuel + 461) acc) := by rfl

theorem array_simplices_chunk_011 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 462) (SourceJson.white (simplicesChunk011Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 461) (SourceJson.white tail) (simplicesChunk011Push00 acc) := by
  have hinput : simplicesChunk011Chars00 ++ tail = simplicesChunk011LeadChars00 ++ (fragment119103Chars00 ++ (simplicesChunk011SuffixChars00 ++ tail)) := by
    simp only [simplicesChunk011Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 462) (SourceJson.white (simplicesChunk011Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 462)
          (SourceJson.white (simplicesChunk011LeadChars00 ++ (fragment119103Chars00 ++ (simplicesChunk011SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 462) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 461) (fragment119103Chars00 ++ (simplicesChunk011SuffixChars00 ++ tail))).bind
        (simplicesChunk011AfterValue00 (fuel + 461) acc) := array_simplices_chunk_011_head fuel (simplicesChunk011SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment119103Value00, simplicesChunk011SuffixChars00 ++ tail)).bind
        (simplicesChunk011AfterValue00 (fuel + 461) acc) :=
      congrArg (fun result => result.bind (simplicesChunk011AfterValue00 (fuel + 461) acc))
        (value_fragment119103 (fuel + 235) (simplicesChunk011SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 461) (SourceJson.white tail) (simplicesChunk011Push00 acc) := by rfl

noncomputable def simplicesArrayAcc01200 : List SourceJson := simplicesChunk011Push00 simplicesArrayAcc01100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_011_generic_complete"
  err.flush

noncomputable def simplicesBlock002Chars00 : List Char := simplicesChunk008Chars00 ++ simplicesChunk009Chars00 ++ simplicesChunk010Chars00 ++ simplicesChunk011Chars00
noncomputable def simplicesBlock002Push00 (acc : List SourceJson) : List SourceJson := simplicesChunk011Push00 (simplicesChunk010Push00 (simplicesChunk009Push00 (simplicesChunk008Push00 (acc))))

theorem array_simplices_block_002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 465)
      (SourceJson.white (simplicesBlock002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 461) (SourceJson.white tail) (simplicesBlock002Push00 acc) := by
  have hinput : simplicesBlock002Chars00 ++ tail = simplicesChunk008Chars00 ++ (simplicesChunk009Chars00 ++ (simplicesChunk010Chars00 ++ (simplicesChunk011Chars00 ++ (tail)))) := by
    simp only [simplicesBlock002Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 465)
        (SourceJson.white (simplicesBlock002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 465) (SourceJson.white (simplicesChunk008Chars00 ++ (simplicesChunk009Chars00 ++ (simplicesChunk010Chars00 ++ (simplicesChunk011Chars00 ++ (tail)))))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 465) (SourceJson.white s) acc) hinput
    _ = SourceJson.array (fuel + 464) (SourceJson.white (simplicesChunk009Chars00 ++ (simplicesChunk010Chars00 ++ (simplicesChunk011Chars00 ++ (tail))))) (simplicesChunk008Push00 (acc)) := array_simplices_chunk_008 fuel (simplicesChunk009Chars00 ++ (simplicesChunk010Chars00 ++ (simplicesChunk011Chars00 ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 463) (SourceJson.white (simplicesChunk010Chars00 ++ (simplicesChunk011Chars00 ++ (tail)))) (simplicesChunk009Push00 (simplicesChunk008Push00 (acc))) := array_simplices_chunk_009 fuel (simplicesChunk010Chars00 ++ (simplicesChunk011Chars00 ++ (tail))) (simplicesChunk008Push00 (acc))
    _ = SourceJson.array (fuel + 462) (SourceJson.white (simplicesChunk011Chars00 ++ (tail))) (simplicesChunk010Push00 (simplicesChunk009Push00 (simplicesChunk008Push00 (acc)))) := array_simplices_chunk_010 fuel (simplicesChunk011Chars00 ++ (tail)) (simplicesChunk009Push00 (simplicesChunk008Push00 (acc)))
    _ = SourceJson.array (fuel + 461) (SourceJson.white tail) (simplicesBlock002Push00 acc) := array_simplices_chunk_011 fuel (tail) (simplicesChunk010Push00 (simplicesChunk009Push00 (simplicesChunk008Push00 (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_block_002_before_single_binding"
  err.flush

theorem geometryChars00_simplices_block_002_prefix :
    (geometryChars00.drop 114185).take 6485 = simplicesBlock002Chars00 := by rfl

theorem geometryChars00_simplices_block_002_split :
    geometryChars00.drop 114185 = simplicesBlock002Chars00 ++ geometryChars00.drop 120670 := by
  calc
    geometryChars00.drop 114185 =
        (geometryChars00.drop 114185).take 6485 ++ (geometryChars00.drop 114185).drop 6485 :=
      (List.take_append_drop 6485 (geometryChars00.drop 114185)).symm
    _ = simplicesBlock002Chars00 ++ (geometryChars00.drop 114185).drop 6485 :=
      congrArg (fun p => p ++ (geometryChars00.drop 114185).drop 6485) geometryChars00_simplices_block_002_prefix
    _ = simplicesBlock002Chars00 ++ geometryChars00.drop 120670 := by rw [List.drop_drop]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_block_002_after_single_binding"
  err.flush

theorem array_simplices_original_block_002 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 465)
      (SourceJson.white (geometryChars00.drop 114185)) acc =
      SourceJson.array (fuel + 461)
        (SourceJson.white (geometryChars00.drop 120670)) (simplicesBlock002Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 465) (SourceJson.white s) acc)
      geometryChars00_simplices_block_002_split).trans (array_simplices_block_002 fuel (geometryChars00.drop 120670) acc)

theorem simplices_array_through_block_002 (fuel : Nat) :
    SourceJson.array (fuel + 473)
      (SourceJson.white (geometryChars00.drop 100434)) [] =
      SourceJson.array (fuel + 461)
        (SourceJson.white (geometryChars00.drop 120670)) simplicesArrayAcc01200 := by
  exact (simplices_array_through_block_001 fuel).trans
    (array_simplices_original_block_002 fuel simplicesArrayAcc00800)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_block_002_complete"
  err.flush

#print axioms array_simplices_chunk_008_head
#print axioms array_simplices_chunk_008
#print axioms array_simplices_chunk_009_head
#print axioms array_simplices_chunk_009
#print axioms array_simplices_chunk_010_head
#print axioms array_simplices_chunk_010
#print axioms array_simplices_chunk_011_head
#print axioms array_simplices_chunk_011
#print axioms array_simplices_block_002
#print axioms geometryChars00_simplices_block_002_prefix
#print axioms geometryChars00_simplices_block_002_split
#print axioms array_simplices_original_block_002
#print axioms simplices_array_through_block_002

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
