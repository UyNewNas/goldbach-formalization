import ImbalancedChen.P2OriginalSaving19FacetVerticesArrayBlock00000

/-! Original facet_vertices block 1/1. Generic small chunks are composed first; exact original bytes are then bound once for the complete block, retaining the original arbitrary tail and accumulator semantics.
Exact original bytes are candidate data; the original reader equations below
are the Lean checks. No whole-file decide or replacement reader is used. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 facetVertices_chunk_004_before_generic"
  err.flush

noncomputable def facetVerticesChunk004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', '\r', '\n', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', '\r', '\n', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def facetVerticesChunk004Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '7'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5'])]) :: (acc))

theorem array_facetVertices_chunk_004 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 29) (SourceJson.white (facetVerticesChunk004Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 27) (SourceJson.white tail) (facetVerticesChunk004Push00 acc) := by
  rfl

noncomputable def facetVerticesArrayAcc00500 : List SourceJson := facetVerticesChunk004Push00 facetVerticesArrayAcc00400

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 facetVertices_chunk_004_generic_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 facetVertices_chunk_005_before_generic"
  err.flush

noncomputable def facetVerticesChunk005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', '\r', '\n', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ']']
noncomputable def facetVerticesChunk005Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '7'])]) :: (acc)

theorem array_facetVertices_chunk_005 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 27) (SourceJson.white (facetVerticesChunk005Chars00 ++ tail)) acc =
      .ok (.arr ((facetVerticesChunk005Push00 acc).reverse), tail) := by
  rfl

noncomputable def facetVerticesArrayAcc00600 : List SourceJson := facetVerticesChunk005Push00 facetVerticesArrayAcc00500

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 facetVertices_chunk_005_generic_complete"
  err.flush

noncomputable def facetVerticesBlock001Chars00 : List Char := facetVerticesChunk004Chars00 ++ facetVerticesChunk005Chars00
noncomputable def facetVerticesBlock001Push00 (acc : List SourceJson) : List SourceJson := facetVerticesChunk005Push00 (facetVerticesChunk004Push00 (acc))

theorem array_facetVertices_block_001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 29)
      (SourceJson.white (facetVerticesBlock001Chars00 ++ tail)) acc =
      .ok (.arr ((facetVerticesBlock001Push00 acc).reverse), tail) := by
  have hinput : facetVerticesBlock001Chars00 ++ tail = facetVerticesChunk004Chars00 ++ (facetVerticesChunk005Chars00 ++ (tail)) := by
    simp only [facetVerticesBlock001Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 29)
        (SourceJson.white (facetVerticesBlock001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 29) (SourceJson.white (facetVerticesChunk004Chars00 ++ (facetVerticesChunk005Chars00 ++ (tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 29) (SourceJson.white s) acc) hinput
    _ = SourceJson.array (fuel + 27) (SourceJson.white (facetVerticesChunk005Chars00 ++ (tail))) (facetVerticesChunk004Push00 (acc)) := array_facetVertices_chunk_004 fuel (facetVerticesChunk005Chars00 ++ (tail)) (acc)
    _ = .ok (.arr ((facetVerticesBlock001Push00 acc).reverse), tail) := array_facetVertices_chunk_005 fuel (tail) (facetVerticesChunk004Push00 (acc))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 facetVertices_block_001_before_single_binding"
  err.flush

theorem geometryChars00_facetVertices_block_001_prefix :
    (geometryChars00.drop 64408).take 812 = facetVerticesBlock001Chars00 := by rfl

theorem geometryChars00_facetVertices_block_001_split :
    geometryChars00.drop 64408 = facetVerticesBlock001Chars00 ++ geometryChars00.drop 65220 := by
  calc
    geometryChars00.drop 64408 =
        (geometryChars00.drop 64408).take 812 ++ (geometryChars00.drop 64408).drop 812 :=
      (List.take_append_drop 812 (geometryChars00.drop 64408)).symm
    _ = facetVerticesBlock001Chars00 ++ (geometryChars00.drop 64408).drop 812 :=
      congrArg (fun p => p ++ (geometryChars00.drop 64408).drop 812) geometryChars00_facetVertices_block_001_prefix
    _ = facetVerticesBlock001Chars00 ++ geometryChars00.drop 65220 := by rw [List.drop_drop]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 facetVertices_block_001_after_single_binding"
  err.flush

theorem array_facetVertices_original_block_001 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 29)
      (SourceJson.white (geometryChars00.drop 64408)) acc =
      .ok (.arr ((facetVerticesBlock001Push00 acc).reverse), geometryChars00.drop 65220) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 29) (SourceJson.white s) acc)
      geometryChars00_facetVertices_block_001_split).trans (array_facetVertices_block_001 fuel (geometryChars00.drop 65220) acc)

noncomputable def facetVerticesArrayValue00 : SourceJson := .arr (facetVerticesArrayAcc00600.reverse)

theorem facetVertices_array_through_block_001 (fuel : Nat) :
    SourceJson.array (fuel + 37)
      (SourceJson.white (geometryChars00.drop 62678)) [] =
      .ok (facetVerticesArrayValue00, geometryChars00.drop 65220) := by
  exact (facetVertices_array_through_block_000 fuel).trans
    (array_facetVertices_original_block_001 fuel facetVerticesArrayAcc00400)

theorem value_facetVertices_original (fuel : Nat) :
    SourceJson.value (fuel + 38) (geometryChars00.drop 62677) =
      .ok (facetVerticesArrayValue00, geometryChars00.drop 65220) := by
  exact (value_facetVertices_open fuel).trans (facetVertices_array_through_block_001 fuel)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 facetVertices_block_001_complete"
  err.flush

#print axioms array_facetVertices_chunk_004
#print axioms array_facetVertices_chunk_005
#print axioms array_facetVertices_block_001
#print axioms geometryChars00_facetVertices_block_001_prefix
#print axioms geometryChars00_facetVertices_block_001_split
#print axioms array_facetVertices_original_block_001
#print axioms facetVertices_array_through_block_001
#print axioms value_facetVertices_original

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
