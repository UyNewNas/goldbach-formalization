import ImbalancedChen.P2OriginalSaving19VerticesArrayBlock00000

/-! Original vertices array block 1/3; small chunks with arbitrary tails and accumulators.
Exact original bytes are candidate data; the original reader equations below
are the Lean checks. No whole-file decide or replacement reader is used. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def verticesChunk004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '5', '1', '5', '6', '2', '1', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '3', '9', '1', '0', '6', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '9', '/', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '7', '8', '1', '2', '9', '/', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '7', '8', '1', '2', '9', '/', '8', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '5', '1', '5', '6', '2', '1', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '7', '0', '3', '3', '9', '3', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '9', '/', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '3', '9', '0', '6', '9', '3', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def verticesChunk004Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.str (String.ofList ['3', '5', '1', '5', '6', '2', '1', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '7', '0', '3', '3', '9', '3', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '9', '/', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '9', '0', '6', '9', '3', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0'])]) :: ((.arr [.str (String.ofList ['3', '5', '1', '5', '6', '2', '1', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '3', '9', '1', '0', '6', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '9', '/', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '7', '8', '1', '2', '9', '/', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '7', '8', '1', '2', '9', '/', '8', '0', '0', '0', '0', '0', '0', '0'])]) :: (acc))
noncomputable def verticesArrayAcc00500 : List SourceJson := verticesChunk004Push00 verticesArrayAcc00400

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertices_chunk_004_before"
  err.flush

theorem geometryChars00_vertices_chunk_004_prefix :
    (geometryChars00.drop 42453).take 461 = verticesChunk004Chars00 := by rfl

theorem geometryChars00_vertices_chunk_004_split :
    geometryChars00.drop 42453 = verticesChunk004Chars00 ++ geometryChars00.drop 42914 := by
  calc
    geometryChars00.drop 42453 =
        (geometryChars00.drop 42453).take 461 ++ (geometryChars00.drop 42453).drop 461 :=
      (List.take_append_drop 461 (geometryChars00.drop 42453)).symm
    _ = verticesChunk004Chars00 ++ (geometryChars00.drop 42453).drop 461 :=
      congrArg (fun p => p ++ (geometryChars00.drop 42453).drop 461) geometryChars00_vertices_chunk_004_prefix
    _ = verticesChunk004Chars00 ++ geometryChars00.drop 42914 := by rw [List.drop_drop]

theorem array_vertices_chunk_004 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 46)
      (SourceJson.white (verticesChunk004Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 44) (SourceJson.white tail)
        (verticesChunk004Push00 acc) := by rfl

theorem array_vertices_original_chunk_004 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 46)
      (SourceJson.white (geometryChars00.drop 42453)) acc =
      SourceJson.array (fuel + 44)
        (SourceJson.white (geometryChars00.drop 42914)) (verticesChunk004Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 46) (SourceJson.white s) acc)
      geometryChars00_vertices_chunk_004_split).trans
    (array_vertices_chunk_004 fuel (geometryChars00.drop 42914) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertices_chunk_004_complete"
  err.flush

noncomputable def verticesChunk005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '4', '4', '3', '7', '1', '/', '6', '2', '4', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '0', '9', '4', '1', '/', '2', '4', '3', '7', '5', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '5', '3', '1', '9', '3', '/', '5', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '8', '5', '9', '1', '6', '3', '/', '1', '5', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '3', '6', '6', '/', '6', '0', '9', '3', '7', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '4', '6', '7', '/', '1', '5', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '0', '3', '1', '2', '1', '/', '5', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '0', '3', '1', '2', '1', '/', '5', '2', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '6', '0', '9', '2', '8', '3', '/', '1', '5', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '1', '8', '8', '3', '/', '4', '8', '7', '5', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '8', '5', '9', '5', '7', '1', '/', '1', '5', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '7', '1', '8', '3', '1', '/', '3', '1', '2', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '0', '6', '1', '9', '/', '3', '2', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '4', '4', '3', '/', '1', '5', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '4', '4', '3', '/', '1', '5', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '0', '3', '1', '1', '3', '/', '5', '2', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def verticesChunk005Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.str (String.ofList ['1', '8', '6', '0', '9', '2', '8', '3', '/', '1', '5', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '1', '8', '8', '3', '/', '4', '8', '7', '5', '0', '0', '0']), .str (String.ofList ['1', '1', '8', '5', '9', '5', '7', '1', '/', '1', '5', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '7', '1', '8', '3', '1', '/', '3', '1', '2', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '0', '6', '1', '9', '/', '3', '2', '5', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '0', '9', '4', '4', '3', '/', '1', '5', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '0', '9', '4', '4', '3', '/', '1', '5', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '0', '3', '1', '1', '3', '/', '5', '2', '0', '0', '0', '0', '0', '0'])]) :: ((.arr [.str (String.ofList ['7', '4', '4', '3', '7', '1', '/', '6', '2', '4', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '0', '9', '4', '1', '/', '2', '4', '3', '7', '5', '0', '0']), .str (String.ofList ['3', '9', '5', '3', '1', '9', '3', '/', '5', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '8', '5', '9', '1', '6', '3', '/', '1', '5', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '3', '6', '6', '/', '6', '0', '9', '3', '7', '5']), .str (String.ofList ['5', '1', '0', '9', '4', '6', '7', '/', '1', '5', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '0', '3', '1', '2', '1', '/', '5', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '0', '3', '1', '2', '1', '/', '5', '2', '0', '0', '0', '0', '0', '0'])]) :: (acc))
noncomputable def verticesArrayAcc00600 : List SourceJson := verticesChunk005Push00 verticesArrayAcc00500

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertices_chunk_005_before"
  err.flush

theorem geometryChars00_vertices_chunk_005_prefix :
    (geometryChars00.drop 42914).take 457 = verticesChunk005Chars00 := by rfl

theorem geometryChars00_vertices_chunk_005_split :
    geometryChars00.drop 42914 = verticesChunk005Chars00 ++ geometryChars00.drop 43371 := by
  calc
    geometryChars00.drop 42914 =
        (geometryChars00.drop 42914).take 457 ++ (geometryChars00.drop 42914).drop 457 :=
      (List.take_append_drop 457 (geometryChars00.drop 42914)).symm
    _ = verticesChunk005Chars00 ++ (geometryChars00.drop 42914).drop 457 :=
      congrArg (fun p => p ++ (geometryChars00.drop 42914).drop 457) geometryChars00_vertices_chunk_005_prefix
    _ = verticesChunk005Chars00 ++ geometryChars00.drop 43371 := by rw [List.drop_drop]

theorem array_vertices_chunk_005 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 44)
      (SourceJson.white (verticesChunk005Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 42) (SourceJson.white tail)
        (verticesChunk005Push00 acc) := by rfl

theorem array_vertices_original_chunk_005 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 44)
      (SourceJson.white (geometryChars00.drop 42914)) acc =
      SourceJson.array (fuel + 42)
        (SourceJson.white (geometryChars00.drop 43371)) (verticesChunk005Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 44) (SourceJson.white s) acc)
      geometryChars00_vertices_chunk_005_split).trans
    (array_vertices_chunk_005 fuel (geometryChars00.drop 43371) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertices_chunk_005_complete"
  err.flush

noncomputable def verticesChunk006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '9', '6', '8', '7', '1', '/', '1', '0', '6', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '9', '5', '3', '1', '3', '7', '/', '2', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '9', '5', '3', '0', '4', '1', '/', '2', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '9', '8', '4', '3', '7', '9', '/', '1', '0', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '9', '8', '4', '3', '7', '9', '/', '2', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '9', '8', '4', '3', '7', '9', '/', '2', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '9', '8', '4', '3', '7', '9', '/', '2', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '9', '6', '8', '7', '1', '/', '4', '2', '4', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '5', '3', '1', '2', '1', '/', '1', '1', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '2', '9', '6', '8', '8', '7', '/', '2', '3', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '2', '9', '6', '7', '9', '1', '/', '2', '3', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '7', '6', '5', '6', '2', '9', '/', '1', '1', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '7', '6', '5', '6', '2', '9', '/', '2', '3', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '7', '6', '5', '6', '2', '9', '/', '2', '3', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '5', '3', '1', '2', '1', '/', '4', '7', '2', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '5', '3', '1', '2', '1', '/', '4', '7', '2', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def verticesChunk006Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.str (String.ofList ['1', '4', '5', '3', '1', '2', '1', '/', '1', '1', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '2', '9', '6', '8', '8', '7', '/', '2', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '2', '9', '6', '7', '9', '1', '/', '2', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '7', '6', '5', '6', '2', '9', '/', '1', '1', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '7', '6', '5', '6', '2', '9', '/', '2', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '7', '6', '5', '6', '2', '9', '/', '2', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '5', '3', '1', '2', '1', '/', '4', '7', '2', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '5', '3', '1', '2', '1', '/', '4', '7', '2', '0', '0', '0', '0', '0'])]) :: ((.arr [.str (String.ofList ['1', '2', '9', '6', '8', '7', '1', '/', '1', '0', '6', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '9', '5', '3', '1', '3', '7', '/', '2', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '9', '5', '3', '0', '4', '1', '/', '2', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '9', '8', '4', '3', '7', '9', '/', '1', '0', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '9', '8', '4', '3', '7', '9', '/', '2', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '9', '8', '4', '3', '7', '9', '/', '2', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '9', '8', '4', '3', '7', '9', '/', '2', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '9', '6', '8', '7', '1', '/', '4', '2', '4', '0', '0', '0', '0', '0'])]) :: (acc))
noncomputable def verticesArrayAcc00700 : List SourceJson := verticesChunk006Push00 verticesArrayAcc00600

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertices_chunk_006_before"
  err.flush

theorem geometryChars00_vertices_chunk_006_prefix :
    (geometryChars00.drop 43371).take 475 = verticesChunk006Chars00 := by rfl

theorem geometryChars00_vertices_chunk_006_split :
    geometryChars00.drop 43371 = verticesChunk006Chars00 ++ geometryChars00.drop 43846 := by
  calc
    geometryChars00.drop 43371 =
        (geometryChars00.drop 43371).take 475 ++ (geometryChars00.drop 43371).drop 475 :=
      (List.take_append_drop 475 (geometryChars00.drop 43371)).symm
    _ = verticesChunk006Chars00 ++ (geometryChars00.drop 43371).drop 475 :=
      congrArg (fun p => p ++ (geometryChars00.drop 43371).drop 475) geometryChars00_vertices_chunk_006_prefix
    _ = verticesChunk006Chars00 ++ geometryChars00.drop 43846 := by rw [List.drop_drop]

theorem array_vertices_chunk_006 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 42)
      (SourceJson.white (verticesChunk006Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 40) (SourceJson.white tail)
        (verticesChunk006Push00 acc) := by rfl

theorem array_vertices_original_chunk_006 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 42)
      (SourceJson.white (geometryChars00.drop 43371)) acc =
      SourceJson.array (fuel + 40)
        (SourceJson.white (geometryChars00.drop 43846)) (verticesChunk006Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 42) (SourceJson.white s) acc)
      geometryChars00_vertices_chunk_006_split).trans
    (array_vertices_chunk_006 fuel (geometryChars00.drop 43846) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertices_chunk_006_complete"
  err.flush

noncomputable def verticesChunk007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '0', '5', '1', '9', '9', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '0', '3', '1', '2', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '6', '1', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '6', '0', '4', '3', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '6', '0', '4', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '6', '0', '4', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '4', '3', '7', '9', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '9', '3', '7', '9', '/', '1', '4', '4', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '7', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '7', '9', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '7', '9', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '7', '9', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def verticesChunk007Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '3', '4', '3', '7', '9', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '9', '3', '7', '9', '/', '1', '4', '4', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '7', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '7', '9', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '7', '9', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '7', '9', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '7', '2', '0', '0', '0', '0', '0', '0'])]) :: ((.arr [.str (String.ofList ['5', '0', '5', '1', '9', '9', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '0', '3', '1', '2', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '6', '1', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '6', '0', '4', '3', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '6', '0', '4', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '6', '0', '4', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0'])]) :: (acc))
noncomputable def verticesArrayAcc00800 : List SourceJson := verticesChunk007Push00 verticesArrayAcc00700

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertices_chunk_007_before"
  err.flush

theorem geometryChars00_vertices_chunk_007_prefix :
    (geometryChars00.drop 43846).take 444 = verticesChunk007Chars00 := by rfl

theorem geometryChars00_vertices_chunk_007_split :
    geometryChars00.drop 43846 = verticesChunk007Chars00 ++ geometryChars00.drop 44290 := by
  calc
    geometryChars00.drop 43846 =
        (geometryChars00.drop 43846).take 444 ++ (geometryChars00.drop 43846).drop 444 :=
      (List.take_append_drop 444 (geometryChars00.drop 43846)).symm
    _ = verticesChunk007Chars00 ++ (geometryChars00.drop 43846).drop 444 :=
      congrArg (fun p => p ++ (geometryChars00.drop 43846).drop 444) geometryChars00_vertices_chunk_007_prefix
    _ = verticesChunk007Chars00 ++ geometryChars00.drop 44290 := by rw [List.drop_drop]

theorem array_vertices_chunk_007 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 40)
      (SourceJson.white (verticesChunk007Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 38) (SourceJson.white tail)
        (verticesChunk007Push00 acc) := by rfl

theorem array_vertices_original_chunk_007 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 40)
      (SourceJson.white (geometryChars00.drop 43846)) acc =
      SourceJson.array (fuel + 38)
        (SourceJson.white (geometryChars00.drop 44290)) (verticesChunk007Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 40) (SourceJson.white s) acc)
      geometryChars00_vertices_chunk_007_split).trans
    (array_vertices_chunk_007 fuel (geometryChars00.drop 44290) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertices_chunk_007_complete"
  err.flush

theorem vertices_array_through_block_001 (fuel : Nat) :
    SourceJson.array (fuel + 54)
      (SourceJson.white (geometryChars00.drop 40615)) [] =
      SourceJson.array (fuel + 38)
        (SourceJson.white (geometryChars00.drop 44290)) verticesArrayAcc00800 := by
  calc
    SourceJson.array (fuel + 54)
        (SourceJson.white (geometryChars00.drop 40615)) [] =
      SourceJson.array (fuel + 46)
        (SourceJson.white (geometryChars00.drop 42453)) verticesArrayAcc00400 :=
      vertices_array_through_block_000 fuel
    _ =
      SourceJson.array (fuel + 44)
        (SourceJson.white (geometryChars00.drop 42914)) verticesArrayAcc00500 :=
      array_vertices_original_chunk_004 fuel verticesArrayAcc00400
    _ =
      SourceJson.array (fuel + 42)
        (SourceJson.white (geometryChars00.drop 43371)) verticesArrayAcc00600 :=
      array_vertices_original_chunk_005 fuel verticesArrayAcc00500
    _ =
      SourceJson.array (fuel + 40)
        (SourceJson.white (geometryChars00.drop 43846)) verticesArrayAcc00700 :=
      array_vertices_original_chunk_006 fuel verticesArrayAcc00600
    _ =
      SourceJson.array (fuel + 38)
        (SourceJson.white (geometryChars00.drop 44290)) verticesArrayAcc00800 :=
      array_vertices_original_chunk_007 fuel verticesArrayAcc00700

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertices_block_001_complete"
  err.flush

#print axioms geometryChars00_vertices_chunk_004_prefix
#print axioms geometryChars00_vertices_chunk_004_split
#print axioms array_vertices_chunk_004
#print axioms array_vertices_original_chunk_004
#print axioms geometryChars00_vertices_chunk_005_prefix
#print axioms geometryChars00_vertices_chunk_005_split
#print axioms array_vertices_chunk_005
#print axioms array_vertices_original_chunk_005
#print axioms geometryChars00_vertices_chunk_006_prefix
#print axioms geometryChars00_vertices_chunk_006_split
#print axioms array_vertices_chunk_006
#print axioms array_vertices_original_chunk_006
#print axioms geometryChars00_vertices_chunk_007_prefix
#print axioms geometryChars00_vertices_chunk_007_split
#print axioms array_vertices_chunk_007
#print axioms array_vertices_original_chunk_007
#print axioms vertices_array_through_block_001

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
