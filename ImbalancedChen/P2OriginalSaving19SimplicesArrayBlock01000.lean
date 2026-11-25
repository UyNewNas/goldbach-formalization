import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00900
import ImbalancedChen.P2OriginalSaving19ValueFragment16832000
import ImbalancedChen.P2OriginalSaving19ValueFragment16982400
import ImbalancedChen.P2OriginalSaving19ValueFragment17167300
import ImbalancedChen.P2OriginalSaving19ValueFragment17331700

/-! Original simplices block 10/13. Generic small chunks are composed first; exact original bytes are then bound once for the complete block, retaining the original arbitrary tail and accumulator semantics.
Exact original bytes are candidate data; the original reader equations below
are the Lean checks. No whole-file decide or replacement reader is used. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_040_before_generic"
  err.flush

noncomputable def simplicesChunk040LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def simplicesChunk040SuffixChars00 : List Char := [',']
noncomputable def simplicesChunk040Chars00 : List Char := simplicesChunk040LeadChars00 ++ fragment168320Chars00 ++ simplicesChunk040SuffixChars00
noncomputable def simplicesChunk040Push00 (acc : List SourceJson) : List SourceJson := fragment168320Value00 :: acc

noncomputable def simplicesChunk040AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_simplices_chunk_040_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 433)
      (SourceJson.white (simplicesChunk040LeadChars00 ++ (fragment168320Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 432) (fragment168320Chars00 ++ rest)).bind
        (simplicesChunk040AfterValue00 (fuel + 432) acc) := by rfl

theorem array_simplices_chunk_040 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 433) (SourceJson.white (simplicesChunk040Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 432) (SourceJson.white tail) (simplicesChunk040Push00 acc) := by
  have hinput : simplicesChunk040Chars00 ++ tail = simplicesChunk040LeadChars00 ++ (fragment168320Chars00 ++ (simplicesChunk040SuffixChars00 ++ tail)) := by
    simp only [simplicesChunk040Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 433) (SourceJson.white (simplicesChunk040Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 433)
          (SourceJson.white (simplicesChunk040LeadChars00 ++ (fragment168320Chars00 ++ (simplicesChunk040SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 433) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 432) (fragment168320Chars00 ++ (simplicesChunk040SuffixChars00 ++ tail))).bind
        (simplicesChunk040AfterValue00 (fuel + 432) acc) := array_simplices_chunk_040_head fuel (simplicesChunk040SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment168320Value00, simplicesChunk040SuffixChars00 ++ tail)).bind
        (simplicesChunk040AfterValue00 (fuel + 432) acc) :=
      congrArg (fun result => result.bind (simplicesChunk040AfterValue00 (fuel + 432) acc))
        (value_fragment168320 (fuel + 231) (simplicesChunk040SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 432) (SourceJson.white tail) (simplicesChunk040Push00 acc) := by rfl

noncomputable def simplicesArrayAcc04100 : List SourceJson := simplicesChunk040Push00 simplicesArrayAcc04000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_040_generic_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_041_before_generic"
  err.flush

noncomputable def simplicesChunk041LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def simplicesChunk041SuffixChars00 : List Char := [',']
noncomputable def simplicesChunk041Chars00 : List Char := simplicesChunk041LeadChars00 ++ fragment169824Chars00 ++ simplicesChunk041SuffixChars00
noncomputable def simplicesChunk041Push00 (acc : List SourceJson) : List SourceJson := fragment169824Value00 :: acc

noncomputable def simplicesChunk041AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_simplices_chunk_041_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 432)
      (SourceJson.white (simplicesChunk041LeadChars00 ++ (fragment169824Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 431) (fragment169824Chars00 ++ rest)).bind
        (simplicesChunk041AfterValue00 (fuel + 431) acc) := by rfl

theorem array_simplices_chunk_041 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 432) (SourceJson.white (simplicesChunk041Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 431) (SourceJson.white tail) (simplicesChunk041Push00 acc) := by
  have hinput : simplicesChunk041Chars00 ++ tail = simplicesChunk041LeadChars00 ++ (fragment169824Chars00 ++ (simplicesChunk041SuffixChars00 ++ tail)) := by
    simp only [simplicesChunk041Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 432) (SourceJson.white (simplicesChunk041Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 432)
          (SourceJson.white (simplicesChunk041LeadChars00 ++ (fragment169824Chars00 ++ (simplicesChunk041SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 432) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 431) (fragment169824Chars00 ++ (simplicesChunk041SuffixChars00 ++ tail))).bind
        (simplicesChunk041AfterValue00 (fuel + 431) acc) := array_simplices_chunk_041_head fuel (simplicesChunk041SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment169824Value00, simplicesChunk041SuffixChars00 ++ tail)).bind
        (simplicesChunk041AfterValue00 (fuel + 431) acc) :=
      congrArg (fun result => result.bind (simplicesChunk041AfterValue00 (fuel + 431) acc))
        (value_fragment169824 (fuel + 75) (simplicesChunk041SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 431) (SourceJson.white tail) (simplicesChunk041Push00 acc) := by rfl

noncomputable def simplicesArrayAcc04200 : List SourceJson := simplicesChunk041Push00 simplicesArrayAcc04100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_041_generic_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_042_before_generic"
  err.flush

noncomputable def simplicesChunk042LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def simplicesChunk042SuffixChars00 : List Char := [',']
noncomputable def simplicesChunk042Chars00 : List Char := simplicesChunk042LeadChars00 ++ fragment171673Chars00 ++ simplicesChunk042SuffixChars00
noncomputable def simplicesChunk042Push00 (acc : List SourceJson) : List SourceJson := fragment171673Value00 :: acc

noncomputable def simplicesChunk042AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_simplices_chunk_042_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 431)
      (SourceJson.white (simplicesChunk042LeadChars00 ++ (fragment171673Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 430) (fragment171673Chars00 ++ rest)).bind
        (simplicesChunk042AfterValue00 (fuel + 430) acc) := by rfl

theorem array_simplices_chunk_042 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 431) (SourceJson.white (simplicesChunk042Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 430) (SourceJson.white tail) (simplicesChunk042Push00 acc) := by
  have hinput : simplicesChunk042Chars00 ++ tail = simplicesChunk042LeadChars00 ++ (fragment171673Chars00 ++ (simplicesChunk042SuffixChars00 ++ tail)) := by
    simp only [simplicesChunk042Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 431) (SourceJson.white (simplicesChunk042Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 431)
          (SourceJson.white (simplicesChunk042LeadChars00 ++ (fragment171673Chars00 ++ (simplicesChunk042SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 431) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 430) (fragment171673Chars00 ++ (simplicesChunk042SuffixChars00 ++ tail))).bind
        (simplicesChunk042AfterValue00 (fuel + 430) acc) := array_simplices_chunk_042_head fuel (simplicesChunk042SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment171673Value00, simplicesChunk042SuffixChars00 ++ tail)).bind
        (simplicesChunk042AfterValue00 (fuel + 430) acc) :=
      congrArg (fun result => result.bind (simplicesChunk042AfterValue00 (fuel + 430) acc))
        (value_fragment171673 (fuel + 178) (simplicesChunk042SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 430) (SourceJson.white tail) (simplicesChunk042Push00 acc) := by rfl

noncomputable def simplicesArrayAcc04300 : List SourceJson := simplicesChunk042Push00 simplicesArrayAcc04200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_042_generic_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_043_before_generic"
  err.flush

noncomputable def simplicesChunk043LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def simplicesChunk043SuffixChars00 : List Char := [',']
noncomputable def simplicesChunk043Chars00 : List Char := simplicesChunk043LeadChars00 ++ fragment173317Chars00 ++ simplicesChunk043SuffixChars00
noncomputable def simplicesChunk043Push00 (acc : List SourceJson) : List SourceJson := fragment173317Value00 :: acc

noncomputable def simplicesChunk043AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_simplices_chunk_043_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 430)
      (SourceJson.white (simplicesChunk043LeadChars00 ++ (fragment173317Chars00 ++ rest))) acc =
      (SourceJson.value (fuel + 429) (fragment173317Chars00 ++ rest)).bind
        (simplicesChunk043AfterValue00 (fuel + 429) acc) := by rfl

theorem array_simplices_chunk_043 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 430) (SourceJson.white (simplicesChunk043Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 429) (SourceJson.white tail) (simplicesChunk043Push00 acc) := by
  have hinput : simplicesChunk043Chars00 ++ tail = simplicesChunk043LeadChars00 ++ (fragment173317Chars00 ++ (simplicesChunk043SuffixChars00 ++ tail)) := by
    simp only [simplicesChunk043Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 430) (SourceJson.white (simplicesChunk043Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 430)
          (SourceJson.white (simplicesChunk043LeadChars00 ++ (fragment173317Chars00 ++ (simplicesChunk043SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 430) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 429) (fragment173317Chars00 ++ (simplicesChunk043SuffixChars00 ++ tail))).bind
        (simplicesChunk043AfterValue00 (fuel + 429) acc) := array_simplices_chunk_043_head fuel (simplicesChunk043SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment173317Value00, simplicesChunk043SuffixChars00 ++ tail)).bind
        (simplicesChunk043AfterValue00 (fuel + 429) acc) :=
      congrArg (fun result => result.bind (simplicesChunk043AfterValue00 (fuel + 429) acc))
        (value_fragment173317 (fuel + 29) (simplicesChunk043SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 429) (SourceJson.white tail) (simplicesChunk043Push00 acc) := by rfl

noncomputable def simplicesArrayAcc04400 : List SourceJson := simplicesChunk043Push00 simplicesArrayAcc04300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_chunk_043_generic_complete"
  err.flush

noncomputable def simplicesBlock010Chars00 : List Char := simplicesChunk040Chars00 ++ simplicesChunk041Chars00 ++ simplicesChunk042Chars00 ++ simplicesChunk043Chars00
noncomputable def simplicesBlock010Push00 (acc : List SourceJson) : List SourceJson := simplicesChunk043Push00 (simplicesChunk042Push00 (simplicesChunk041Push00 (simplicesChunk040Push00 (acc))))

theorem array_simplices_block_010 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 433)
      (SourceJson.white (simplicesBlock010Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 429) (SourceJson.white tail) (simplicesBlock010Push00 acc) := by
  have hinput : simplicesBlock010Chars00 ++ tail = simplicesChunk040Chars00 ++ (simplicesChunk041Chars00 ++ (simplicesChunk042Chars00 ++ (simplicesChunk043Chars00 ++ (tail)))) := by
    simp only [simplicesBlock010Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 433)
        (SourceJson.white (simplicesBlock010Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 433) (SourceJson.white (simplicesChunk040Chars00 ++ (simplicesChunk041Chars00 ++ (simplicesChunk042Chars00 ++ (simplicesChunk043Chars00 ++ (tail)))))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 433) (SourceJson.white s) acc) hinput
    _ = SourceJson.array (fuel + 432) (SourceJson.white (simplicesChunk041Chars00 ++ (simplicesChunk042Chars00 ++ (simplicesChunk043Chars00 ++ (tail))))) (simplicesChunk040Push00 (acc)) := array_simplices_chunk_040 fuel (simplicesChunk041Chars00 ++ (simplicesChunk042Chars00 ++ (simplicesChunk043Chars00 ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 431) (SourceJson.white (simplicesChunk042Chars00 ++ (simplicesChunk043Chars00 ++ (tail)))) (simplicesChunk041Push00 (simplicesChunk040Push00 (acc))) := array_simplices_chunk_041 fuel (simplicesChunk042Chars00 ++ (simplicesChunk043Chars00 ++ (tail))) (simplicesChunk040Push00 (acc))
    _ = SourceJson.array (fuel + 430) (SourceJson.white (simplicesChunk043Chars00 ++ (tail))) (simplicesChunk042Push00 (simplicesChunk041Push00 (simplicesChunk040Push00 (acc)))) := array_simplices_chunk_042 fuel (simplicesChunk043Chars00 ++ (tail)) (simplicesChunk041Push00 (simplicesChunk040Push00 (acc)))
    _ = SourceJson.array (fuel + 429) (SourceJson.white tail) (simplicesBlock010Push00 acc) := array_simplices_chunk_043 fuel (tail) (simplicesChunk042Push00 (simplicesChunk041Push00 (simplicesChunk040Push00 (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_block_010_before_single_binding"
  err.flush

theorem geometryChars00_simplices_block_010_prefix :
    (geometryChars00.drop 168314).take 6966 = simplicesBlock010Chars00 := by rfl

theorem geometryChars00_simplices_block_010_split :
    geometryChars00.drop 168314 = simplicesBlock010Chars00 ++ geometryChars00.drop 175280 := by
  calc
    geometryChars00.drop 168314 =
        (geometryChars00.drop 168314).take 6966 ++ (geometryChars00.drop 168314).drop 6966 :=
      (List.take_append_drop 6966 (geometryChars00.drop 168314)).symm
    _ = simplicesBlock010Chars00 ++ (geometryChars00.drop 168314).drop 6966 :=
      congrArg (fun p => p ++ (geometryChars00.drop 168314).drop 6966) geometryChars00_simplices_block_010_prefix
    _ = simplicesBlock010Chars00 ++ geometryChars00.drop 175280 := by rw [List.drop_drop]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_block_010_after_single_binding"
  err.flush

theorem array_simplices_original_block_010 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 433)
      (SourceJson.white (geometryChars00.drop 168314)) acc =
      SourceJson.array (fuel + 429)
        (SourceJson.white (geometryChars00.drop 175280)) (simplicesBlock010Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 433) (SourceJson.white s) acc)
      geometryChars00_simplices_block_010_split).trans (array_simplices_block_010 fuel (geometryChars00.drop 175280) acc)

theorem simplices_array_through_block_010 (fuel : Nat) :
    SourceJson.array (fuel + 473)
      (SourceJson.white (geometryChars00.drop 100434)) [] =
      SourceJson.array (fuel + 429)
        (SourceJson.white (geometryChars00.drop 175280)) simplicesArrayAcc04400 := by
  exact (simplices_array_through_block_009 fuel).trans
    (array_simplices_original_block_010 fuel simplicesArrayAcc04000)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 simplices_block_010_complete"
  err.flush

#print axioms array_simplices_chunk_040_head
#print axioms array_simplices_chunk_040
#print axioms array_simplices_chunk_041_head
#print axioms array_simplices_chunk_041
#print axioms array_simplices_chunk_042_head
#print axioms array_simplices_chunk_042
#print axioms array_simplices_chunk_043_head
#print axioms array_simplices_chunk_043
#print axioms array_simplices_block_010
#print axioms geometryChars00_simplices_block_010_prefix
#print axioms geometryChars00_simplices_block_010_split
#print axioms array_simplices_original_block_010
#print axioms simplices_array_through_block_010

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
