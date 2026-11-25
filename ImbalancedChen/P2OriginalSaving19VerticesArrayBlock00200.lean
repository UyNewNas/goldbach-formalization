import ImbalancedChen.P2OriginalSaving19VerticesArrayBlock00100

/-! Original vertices array block 2/3; small chunks with arbitrary tails and accumulators.
Exact original bytes are candidate data; the original reader equations below
are the Lean checks. No whole-file decide or replacement reader is used. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def verticesChunk008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '3', '2', '3', '/', '2', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '2', '7', '8', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '5', '5', '3', '3', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '0', '9', '2', '7', '/', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '0', '9', '2', '7', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '0', '9', '2', '7', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '0', '9', '2', '7', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '3', '6', '8', '7', '/', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '7', '1', '8', '4', '3', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '9', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '7', '1', '8', '7', '1', '/', '8', '4', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '4', '4', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '4', '4', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '4', '4', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '2', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def verticesChunk008Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.str (String.ofList ['2', '6', '7', '1', '8', '4', '3', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '7', '1', '8', '7', '1', '/', '8', '4', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '4', '4', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '4', '4', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '4', '4', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '2', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0'])]) :: ((.arr [.str (String.ofList ['2', '5', '3', '2', '3', '/', '2', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '2', '7', '8', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '5', '5', '3', '3', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '0', '9', '2', '7', '/', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '0', '9', '2', '7', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '0', '9', '2', '7', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '0', '9', '2', '7', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '3', '6', '8', '7', '/', '4', '0', '0', '0', '0', '0', '0'])]) :: (acc))
noncomputable def verticesArrayAcc00900 : List SourceJson := verticesChunk008Push00 verticesArrayAcc00800

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertices_chunk_008_before"
  err.flush

theorem geometryChars00_vertices_chunk_008_prefix :
    (geometryChars00.drop 44290).take 439 = verticesChunk008Chars00 := by rfl

theorem geometryChars00_vertices_chunk_008_split :
    geometryChars00.drop 44290 = verticesChunk008Chars00 ++ geometryChars00.drop 44729 := by
  calc
    geometryChars00.drop 44290 =
        (geometryChars00.drop 44290).take 439 ++ (geometryChars00.drop 44290).drop 439 :=
      (List.take_append_drop 439 (geometryChars00.drop 44290)).symm
    _ = verticesChunk008Chars00 ++ (geometryChars00.drop 44290).drop 439 :=
      congrArg (fun p => p ++ (geometryChars00.drop 44290).drop 439) geometryChars00_vertices_chunk_008_prefix
    _ = verticesChunk008Chars00 ++ geometryChars00.drop 44729 := by rw [List.drop_drop]

theorem array_vertices_chunk_008 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 38)
      (SourceJson.white (verticesChunk008Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 36) (SourceJson.white tail)
        (verticesChunk008Push00 acc) := by rfl

theorem array_vertices_original_chunk_008 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 38)
      (SourceJson.white (geometryChars00.drop 44290)) acc =
      SourceJson.array (fuel + 36)
        (SourceJson.white (geometryChars00.drop 44729)) (verticesChunk008Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 38) (SourceJson.white s) acc)
      geometryChars00_vertices_chunk_008_split).trans
    (array_vertices_chunk_008 fuel (geometryChars00.drop 44729) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertices_chunk_008_complete"
  err.flush

noncomputable def verticesChunk009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '8', '1', '2', '3', '/', '1', '4', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '9', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '5', '3', '1', '1', '7', '/', '1', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '4', '5', '1', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '4', '5', '1', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '9', '6', '8', '7', '9', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '9', '6', '8', '7', '9', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '8', '1', '2', '3', '/', '1', '4', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '4', '6', '8', '8', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '8', '1', '1', '9', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '1', '5', '6', '2', '7', '/', '1', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '1', '5', '6', '2', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '1', '5', '6', '2', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '3', '1', '2', '7', '/', '5', '6', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '3', '1', '2', '7', '/', '5', '6', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def verticesChunk009Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.str (String.ofList ['1', '7', '8', '1', '2', '3', '/', '1', '4', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '4', '6', '8', '8', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '8', '1', '1', '9', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '1', '5', '6', '2', '7', '/', '1', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '1', '5', '6', '2', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '1', '5', '6', '2', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '3', '1', '2', '7', '/', '5', '6', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '3', '1', '2', '7', '/', '5', '6', '0', '0', '0', '0', '0'])]) :: ((.arr [.str (String.ofList ['1', '7', '8', '1', '2', '3', '/', '1', '4', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '5', '3', '1', '1', '7', '/', '1', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '4', '5', '1', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '4', '5', '1', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '9', '6', '8', '7', '9', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '9', '6', '8', '7', '9', '/', '1', '6', '8', '0', '0', '0', '0', '0'])]) :: (acc))
noncomputable def verticesArrayAcc01000 : List SourceJson := verticesChunk009Push00 verticesArrayAcc00900

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertices_chunk_009_before"
  err.flush

theorem geometryChars00_vertices_chunk_009_prefix :
    (geometryChars00.drop 44729).take 444 = verticesChunk009Chars00 := by rfl

theorem geometryChars00_vertices_chunk_009_split :
    geometryChars00.drop 44729 = verticesChunk009Chars00 ++ geometryChars00.drop 45173 := by
  calc
    geometryChars00.drop 44729 =
        (geometryChars00.drop 44729).take 444 ++ (geometryChars00.drop 44729).drop 444 :=
      (List.take_append_drop 444 (geometryChars00.drop 44729)).symm
    _ = verticesChunk009Chars00 ++ (geometryChars00.drop 44729).drop 444 :=
      congrArg (fun p => p ++ (geometryChars00.drop 44729).drop 444) geometryChars00_vertices_chunk_009_prefix
    _ = verticesChunk009Chars00 ++ geometryChars00.drop 45173 := by rw [List.drop_drop]

theorem array_vertices_chunk_009 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 36)
      (SourceJson.white (verticesChunk009Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 34) (SourceJson.white tail)
        (verticesChunk009Push00 acc) := by rfl

theorem array_vertices_original_chunk_009 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 36)
      (SourceJson.white (geometryChars00.drop 44729)) acc =
      SourceJson.array (fuel + 34)
        (SourceJson.white (geometryChars00.drop 45173)) (verticesChunk009Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 36) (SourceJson.white s) acc)
      geometryChars00_vertices_chunk_009_split).trans
    (array_vertices_chunk_009 fuel (geometryChars00.drop 45173) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertices_chunk_009_complete"
  err.flush

noncomputable def verticesChunk010Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '7', '1', '8', '4', '7', '/', '1', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '8', '9', '0', '5', '8', '9', '/', '6', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '5', '6', '2', '1', '/', '2', '7', '2', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '8', '6', '3', '/', '3', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '8', '6', '3', '/', '6', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '8', '6', '3', '/', '6', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '8', '6', '3', '/', '6', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '5', '9', '3', '8', '7', '/', '1', '3', '6', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '6', '7', '9', '/', '2', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '0', '1', '4', '9', '3', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '9', '7', '4', '9', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '3', '8', '3', '1', '/', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '3', '8', '3', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '3', '8', '3', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '4', '1', '9', '/', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '4', '1', '9', '/', '8', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def verticesChunk010Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.str (String.ofList ['2', '5', '6', '7', '9', '/', '2', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '0', '1', '4', '9', '3', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '9', '7', '4', '9', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '3', '8', '3', '1', '/', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '3', '8', '3', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '3', '8', '3', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '4', '1', '9', '/', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '4', '1', '9', '/', '8', '0', '0', '0', '0', '0'])]) :: ((.arr [.str (String.ofList ['2', '1', '7', '1', '8', '4', '7', '/', '1', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '8', '9', '0', '5', '8', '9', '/', '6', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '5', '6', '2', '1', '/', '2', '7', '2', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '8', '6', '3', '/', '3', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '8', '6', '3', '/', '6', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '8', '6', '3', '/', '6', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '8', '6', '3', '/', '6', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '9', '3', '8', '7', '/', '1', '3', '6', '0', '0', '0', '0', '0'])]) :: (acc))
noncomputable def verticesArrayAcc01100 : List SourceJson := verticesChunk010Push00 verticesArrayAcc01000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertices_chunk_010_before"
  err.flush

theorem geometryChars00_vertices_chunk_010_prefix :
    (geometryChars00.drop 45173).take 435 = verticesChunk010Chars00 := by rfl

theorem geometryChars00_vertices_chunk_010_split :
    geometryChars00.drop 45173 = verticesChunk010Chars00 ++ geometryChars00.drop 45608 := by
  calc
    geometryChars00.drop 45173 =
        (geometryChars00.drop 45173).take 435 ++ (geometryChars00.drop 45173).drop 435 :=
      (List.take_append_drop 435 (geometryChars00.drop 45173)).symm
    _ = verticesChunk010Chars00 ++ (geometryChars00.drop 45173).drop 435 :=
      congrArg (fun p => p ++ (geometryChars00.drop 45173).drop 435) geometryChars00_vertices_chunk_010_prefix
    _ = verticesChunk010Chars00 ++ geometryChars00.drop 45608 := by rw [List.drop_drop]

theorem array_vertices_chunk_010 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 34)
      (SourceJson.white (verticesChunk010Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 32) (SourceJson.white tail)
        (verticesChunk010Push00 acc) := by rfl

theorem array_vertices_original_chunk_010 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 34)
      (SourceJson.white (geometryChars00.drop 45173)) acc =
      SourceJson.array (fuel + 32)
        (SourceJson.white (geometryChars00.drop 45608)) (verticesChunk010Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 34) (SourceJson.white s) acc)
      geometryChars00_vertices_chunk_010_split).trans
    (array_vertices_chunk_010 fuel (geometryChars00.drop 45608) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertices_chunk_010_complete"
  err.flush

noncomputable def verticesChunk011Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '9', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '9', '/', '1', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '7', '1', '/', '7', '2', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '7', '1', '/', '7', '2', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '9', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '9', '/', '1', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '7', '1', '/', '7', '2', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def verticesChunk011Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.str (String.ofList ['2', '3', '4', '3', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '1', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '3', '7', '1', '/', '7', '2', '0', '0', '0', '0', '0'])]) :: ((.arr [.str (String.ofList ['2', '3', '4', '3', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '1', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '3', '7', '1', '/', '7', '2', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '3', '7', '1', '/', '7', '2', '0', '0', '0', '0', '0'])]) :: (acc))
noncomputable def verticesArrayAcc01200 : List SourceJson := verticesChunk011Push00 verticesArrayAcc01100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertices_chunk_011_before"
  err.flush

theorem geometryChars00_vertices_chunk_011_prefix :
    (geometryChars00.drop 45608).take 450 = verticesChunk011Chars00 := by rfl

theorem geometryChars00_vertices_chunk_011_split :
    geometryChars00.drop 45608 = verticesChunk011Chars00 ++ geometryChars00.drop 46058 := by
  calc
    geometryChars00.drop 45608 =
        (geometryChars00.drop 45608).take 450 ++ (geometryChars00.drop 45608).drop 450 :=
      (List.take_append_drop 450 (geometryChars00.drop 45608)).symm
    _ = verticesChunk011Chars00 ++ (geometryChars00.drop 45608).drop 450 :=
      congrArg (fun p => p ++ (geometryChars00.drop 45608).drop 450) geometryChars00_vertices_chunk_011_prefix
    _ = verticesChunk011Chars00 ++ geometryChars00.drop 46058 := by rw [List.drop_drop]

theorem array_vertices_chunk_011 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 32)
      (SourceJson.white (verticesChunk011Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 30) (SourceJson.white tail)
        (verticesChunk011Push00 acc) := by rfl

theorem array_vertices_original_chunk_011 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 32)
      (SourceJson.white (geometryChars00.drop 45608)) acc =
      SourceJson.array (fuel + 30)
        (SourceJson.white (geometryChars00.drop 46058)) (verticesChunk011Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 32) (SourceJson.white s) acc)
      geometryChars00_vertices_chunk_011_split).trans
    (array_vertices_chunk_011 fuel (geometryChars00.drop 46058) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertices_chunk_011_complete"
  err.flush

theorem vertices_array_through_block_002 (fuel : Nat) :
    SourceJson.array (fuel + 54)
      (SourceJson.white (geometryChars00.drop 40615)) [] =
      SourceJson.array (fuel + 30)
        (SourceJson.white (geometryChars00.drop 46058)) verticesArrayAcc01200 := by
  calc
    SourceJson.array (fuel + 54)
        (SourceJson.white (geometryChars00.drop 40615)) [] =
      SourceJson.array (fuel + 38)
        (SourceJson.white (geometryChars00.drop 44290)) verticesArrayAcc00800 :=
      vertices_array_through_block_001 fuel
    _ =
      SourceJson.array (fuel + 36)
        (SourceJson.white (geometryChars00.drop 44729)) verticesArrayAcc00900 :=
      array_vertices_original_chunk_008 fuel verticesArrayAcc00800
    _ =
      SourceJson.array (fuel + 34)
        (SourceJson.white (geometryChars00.drop 45173)) verticesArrayAcc01000 :=
      array_vertices_original_chunk_009 fuel verticesArrayAcc00900
    _ =
      SourceJson.array (fuel + 32)
        (SourceJson.white (geometryChars00.drop 45608)) verticesArrayAcc01100 :=
      array_vertices_original_chunk_010 fuel verticesArrayAcc01000
    _ =
      SourceJson.array (fuel + 30)
        (SourceJson.white (geometryChars00.drop 46058)) verticesArrayAcc01200 :=
      array_vertices_original_chunk_011 fuel verticesArrayAcc01100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertices_block_002_complete"
  err.flush

#print axioms geometryChars00_vertices_chunk_008_prefix
#print axioms geometryChars00_vertices_chunk_008_split
#print axioms array_vertices_chunk_008
#print axioms array_vertices_original_chunk_008
#print axioms geometryChars00_vertices_chunk_009_prefix
#print axioms geometryChars00_vertices_chunk_009_split
#print axioms array_vertices_chunk_009
#print axioms array_vertices_original_chunk_009
#print axioms geometryChars00_vertices_chunk_010_prefix
#print axioms geometryChars00_vertices_chunk_010_split
#print axioms array_vertices_chunk_010
#print axioms array_vertices_original_chunk_010
#print axioms geometryChars00_vertices_chunk_011_prefix
#print axioms geometryChars00_vertices_chunk_011_split
#print axioms array_vertices_chunk_011
#print axioms array_vertices_original_chunk_011
#print axioms vertices_array_through_block_002

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
