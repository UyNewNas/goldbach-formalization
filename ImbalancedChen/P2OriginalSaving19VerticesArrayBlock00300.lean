import ImbalancedChen.P2OriginalSaving19VerticesArrayBlock00200

/-! Original vertices array block 3/3; small chunks with arbitrary tails and accumulators.
Exact original bytes are candidate data; the original reader equations below
are the Lean checks. No whole-file decide or replacement reader is used. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def verticesChunk012Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '6', '6', '5', '5', '9', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '6', '5', '5', '8', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '9', '/', '1', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '6', '8', '7', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '2', '1', '9', '1', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '4', '3', '7', '9', '/', '7', '2', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '4', '3', '7', '9', '/', '7', '2', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '2', '8', '0', '0', '9', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '8', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '9', '/', '1', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '0', '3', '0', '7', '3', '/', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '5', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '5', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '4', '5', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def verticesChunk012Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.str (String.ofList ['2', '3', '4', '3', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '8', '0', '0', '9', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '8', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '1', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '0', '3', '0', '7', '3', '/', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '0', '9', '5', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '0', '9', '5', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '0', '9', '4', '5', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0'])]) :: ((.arr [.str (String.ofList ['2', '3', '4', '3', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '6', '6', '5', '5', '9', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '3', '6', '5', '5', '8', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '1', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '6', '8', '7', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '2', '1', '9', '1', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '4', '3', '7', '9', '/', '7', '2', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '4', '3', '7', '9', '/', '7', '2', '0', '0', '0', '0', '0'])]) :: (acc))
noncomputable def verticesArrayAcc01300 : List SourceJson := verticesChunk012Push00 verticesArrayAcc01200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertices_chunk_012_before"
  err.flush

theorem geometryChars00_vertices_chunk_012_prefix :
    (geometryChars00.drop 46058).take 457 = verticesChunk012Chars00 := by rfl

theorem geometryChars00_vertices_chunk_012_split :
    geometryChars00.drop 46058 = verticesChunk012Chars00 ++ geometryChars00.drop 46515 := by
  calc
    geometryChars00.drop 46058 =
        (geometryChars00.drop 46058).take 457 ++ (geometryChars00.drop 46058).drop 457 :=
      (List.take_append_drop 457 (geometryChars00.drop 46058)).symm
    _ = verticesChunk012Chars00 ++ (geometryChars00.drop 46058).drop 457 :=
      congrArg (fun p => p ++ (geometryChars00.drop 46058).drop 457) geometryChars00_vertices_chunk_012_prefix
    _ = verticesChunk012Chars00 ++ geometryChars00.drop 46515 := by rw [List.drop_drop]

theorem array_vertices_chunk_012 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 30)
      (SourceJson.white (verticesChunk012Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 28) (SourceJson.white tail)
        (verticesChunk012Push00 acc) := by rfl

theorem array_vertices_original_chunk_012 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 30)
      (SourceJson.white (geometryChars00.drop 46058)) acc =
      SourceJson.array (fuel + 28)
        (SourceJson.white (geometryChars00.drop 46515)) (verticesChunk012Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 30) (SourceJson.white s) acc)
      geometryChars00_vertices_chunk_012_split).trans
    (array_vertices_chunk_012 fuel (geometryChars00.drop 46515) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertices_chunk_012_complete"
  err.flush

noncomputable def verticesChunk013Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '7', '1', '8', '5', '9', '/', '4', '2', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '9', '5', '2', '9', '5', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '4', '5', '3', '1', '2', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '4', '5', '1', '/', '4', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '4', '5', '1', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '4', '5', '1', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '9', '6', '8', '7', '9', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '9', '6', '8', '7', '9', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '9', '5', '2', '9', '7', '7', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '9', '0', '6', '2', '1', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '4', '4', '3', '/', '4', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '4', '4', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '4', '4', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '4', '4', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '2', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ']']
noncomputable def verticesChunk013Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '9', '5', '2', '9', '7', '7', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '9', '0', '6', '2', '1', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '4', '4', '3', '/', '4', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '4', '4', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '4', '4', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '4', '4', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '2', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0'])]) :: ((.arr [.str (String.ofList ['5', '7', '1', '8', '5', '9', '/', '4', '2', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '9', '5', '2', '9', '5', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '4', '5', '3', '1', '2', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '4', '5', '1', '/', '4', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '4', '5', '1', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '4', '5', '1', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '9', '6', '8', '7', '9', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '9', '6', '8', '7', '9', '/', '1', '6', '8', '0', '0', '0', '0', '0'])]) :: (acc))
noncomputable def verticesArrayAcc01400 : List SourceJson := verticesChunk013Push00 verticesArrayAcc01300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertices_chunk_013_before"
  err.flush

theorem geometryChars00_vertices_chunk_013_prefix :
    (geometryChars00.drop 46515).take 459 = verticesChunk013Chars00 := by rfl

theorem geometryChars00_vertices_chunk_013_split :
    geometryChars00.drop 46515 = verticesChunk013Chars00 ++ geometryChars00.drop 46974 := by
  calc
    geometryChars00.drop 46515 =
        (geometryChars00.drop 46515).take 459 ++ (geometryChars00.drop 46515).drop 459 :=
      (List.take_append_drop 459 (geometryChars00.drop 46515)).symm
    _ = verticesChunk013Chars00 ++ (geometryChars00.drop 46515).drop 459 :=
      congrArg (fun p => p ++ (geometryChars00.drop 46515).drop 459) geometryChars00_vertices_chunk_013_prefix
    _ = verticesChunk013Chars00 ++ geometryChars00.drop 46974 := by rw [List.drop_drop]

theorem array_vertices_chunk_013 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 28)
      (SourceJson.white (verticesChunk013Chars00 ++ tail)) acc =
      .ok (.arr ((verticesChunk013Push00 acc).reverse), tail) := by rfl

theorem array_vertices_original_chunk_013 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 28)
      (SourceJson.white (geometryChars00.drop 46515)) acc =
      .ok (.arr ((verticesChunk013Push00 acc).reverse), geometryChars00.drop 46974) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 28) (SourceJson.white s) acc)
      geometryChars00_vertices_chunk_013_split).trans
    (array_vertices_chunk_013 fuel (geometryChars00.drop 46974) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertices_chunk_013_complete"
  err.flush

noncomputable def verticesArrayValue00 : SourceJson := .arr (verticesArrayAcc01400.reverse)

theorem vertices_array_through_block_003 (fuel : Nat) :
    SourceJson.array (fuel + 54)
      (SourceJson.white (geometryChars00.drop 40615)) [] =
      .ok (verticesArrayValue00, geometryChars00.drop 46974) := by
  calc
    SourceJson.array (fuel + 54)
        (SourceJson.white (geometryChars00.drop 40615)) [] =
      SourceJson.array (fuel + 30)
        (SourceJson.white (geometryChars00.drop 46058)) verticesArrayAcc01200 :=
      vertices_array_through_block_002 fuel
    _ =
      SourceJson.array (fuel + 28)
        (SourceJson.white (geometryChars00.drop 46515)) verticesArrayAcc01300 :=
      array_vertices_original_chunk_012 fuel verticesArrayAcc01200
    _ =
      .ok (verticesArrayValue00, geometryChars00.drop 46974) :=
      array_vertices_original_chunk_013 fuel verticesArrayAcc01300

theorem value_vertices_original (fuel : Nat) :
    SourceJson.value (fuel + 55) (geometryChars00.drop 40614) =
      .ok (verticesArrayValue00, geometryChars00.drop 46974) := by
  exact (value_vertices_open fuel).trans (vertices_array_through_block_003 fuel)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertices_block_003_complete"
  err.flush

#print axioms geometryChars00_vertices_chunk_012_prefix
#print axioms geometryChars00_vertices_chunk_012_split
#print axioms array_vertices_chunk_012
#print axioms array_vertices_original_chunk_012
#print axioms geometryChars00_vertices_chunk_013_prefix
#print axioms geometryChars00_vertices_chunk_013_split
#print axioms array_vertices_chunk_013
#print axioms array_vertices_original_chunk_013
#print axioms vertices_array_through_block_003
#print axioms value_vertices_original

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
