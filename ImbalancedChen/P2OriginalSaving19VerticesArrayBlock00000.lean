import ImbalancedChen.P2OriginalSaving19Active8Field00

/-! Original vertices array block 0/3; small chunks with arbitrary tails and accumulators.
Exact original bytes are candidate data; the original reader equations below
are the Lean checks. No whole-file decide or replacement reader is used. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def verticesOpenChars00 : List Char := ['[']
noncomputable def verticesArrayAcc00000 : List SourceJson := []

theorem geometryChars00_vertices_open_prefix :
    (geometryChars00.drop 40614).take 1 = verticesOpenChars00 := by rfl

theorem geometryChars00_vertices_open_split :
    geometryChars00.drop 40614 = verticesOpenChars00 ++ geometryChars00.drop 40615 := by
  calc
    geometryChars00.drop 40614 =
        (geometryChars00.drop 40614).take 1 ++ (geometryChars00.drop 40614).drop 1 :=
      (List.take_append_drop 1 (geometryChars00.drop 40614)).symm
    _ = verticesOpenChars00 ++ (geometryChars00.drop 40614).drop 1 :=
      congrArg (fun p => p ++ (geometryChars00.drop 40614).drop 1) geometryChars00_vertices_open_prefix
    _ = verticesOpenChars00 ++ geometryChars00.drop 40615 := by rw [List.drop_drop]

theorem value_vertices_open (fuel : Nat) :
    SourceJson.value (fuel + 55) (geometryChars00.drop 40614) =
      SourceJson.array (fuel + 54)
        (SourceJson.white (geometryChars00.drop 40615)) [] := by
  calc
    SourceJson.value (fuel + 55) (geometryChars00.drop 40614) =
        SourceJson.value (fuel + 55)
          (verticesOpenChars00 ++ geometryChars00.drop 40615) :=
      congrArg (SourceJson.value (fuel + 55)) geometryChars00_vertices_open_split
    _ = SourceJson.array (fuel + 54)
        (SourceJson.white (geometryChars00.drop 40615)) [] := by rfl

noncomputable def verticesChunk000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '5', '4', '6', '9', '2', '7', '/', '1', '4', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '5', '7', '8', '5', '5', '3', '/', '1', '4', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '5', '7', '8', '1', '6', '9', '/', '1', '4', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '1', '5', '5', '5', '7', '/', '2', '8', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '7', '9', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '7', '9', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '7', '9', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '0', '3', '1', '2', '9', '/', '9', '6', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '7', '3', '0', '1', '/', '3', '2', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '5', '9', '3', '8', '7', '/', '4', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '5', '9', '2', '5', '9', '/', '4', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '6', '0', '4', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '6', '0', '4', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def verticesChunk000Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.str (String.ofList ['1', '1', '0', '3', '1', '2', '9', '/', '9', '6', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '7', '3', '0', '1', '/', '3', '2', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '5', '9', '3', '8', '7', '/', '4', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '5', '9', '2', '5', '9', '/', '4', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '6', '0', '4', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '6', '0', '4', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0'])]) :: ((.arr [.str (String.ofList ['1', '6', '5', '4', '6', '9', '2', '7', '/', '1', '4', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '5', '7', '8', '5', '5', '3', '/', '1', '4', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '5', '7', '8', '1', '6', '9', '/', '1', '4', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '1', '5', '5', '5', '7', '/', '2', '8', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '7', '9', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '7', '9', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '7', '9', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '7', '2', '0', '0', '0', '0', '0', '0'])]) :: (acc))
noncomputable def verticesArrayAcc00100 : List SourceJson := verticesChunk000Push00 verticesArrayAcc00000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertices_chunk_000_before"
  err.flush

theorem geometryChars00_vertices_chunk_000_prefix :
    (geometryChars00.drop 40615).take 457 = verticesChunk000Chars00 := by rfl

theorem geometryChars00_vertices_chunk_000_split :
    geometryChars00.drop 40615 = verticesChunk000Chars00 ++ geometryChars00.drop 41072 := by
  calc
    geometryChars00.drop 40615 =
        (geometryChars00.drop 40615).take 457 ++ (geometryChars00.drop 40615).drop 457 :=
      (List.take_append_drop 457 (geometryChars00.drop 40615)).symm
    _ = verticesChunk000Chars00 ++ (geometryChars00.drop 40615).drop 457 :=
      congrArg (fun p => p ++ (geometryChars00.drop 40615).drop 457) geometryChars00_vertices_chunk_000_prefix
    _ = verticesChunk000Chars00 ++ geometryChars00.drop 41072 := by rw [List.drop_drop]

theorem array_vertices_chunk_000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 54)
      (SourceJson.white (verticesChunk000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 52) (SourceJson.white tail)
        (verticesChunk000Push00 acc) := by rfl

theorem array_vertices_original_chunk_000 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 54)
      (SourceJson.white (geometryChars00.drop 40615)) acc =
      SourceJson.array (fuel + 52)
        (SourceJson.white (geometryChars00.drop 41072)) (verticesChunk000Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 54) (SourceJson.white s) acc)
      geometryChars00_vertices_chunk_000_split).trans
    (array_vertices_chunk_000 fuel (geometryChars00.drop 41072) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertices_chunk_000_complete"
  err.flush

noncomputable def verticesChunk001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '2', '6', '5', '6', '2', '1', '/', '2', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '4', '3', '7', '9', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '4', '5', '3', '1', '3', '7', '/', '1', '0', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '5', '9', '3', '4', '7', '/', '1', '0', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '5', '9', '3', '4', '7', '/', '2', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '5', '9', '3', '4', '7', '/', '2', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '5', '9', '3', '4', '7', '/', '2', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '0', '3', '1', '1', '3', '/', '5', '2', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '6', '0', '9', '3', '7', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '3', '2', '8', '1', '7', '7', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '7', '8', '1', '2', '9', '/', '3', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '1', '4', '0', '5', '9', '7', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '1', '4', '0', '5', '9', '7', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '1', '4', '0', '5', '9', '7', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '6', '5', '6', '1', '7', '/', '3', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '6', '5', '6', '1', '7', '/', '3', '8', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def verticesChunk001Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.str (String.ofList ['2', '6', '6', '0', '9', '3', '7', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '3', '2', '8', '1', '7', '7', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '0', '7', '8', '1', '2', '9', '/', '3', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '1', '4', '0', '5', '9', '7', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '1', '4', '0', '5', '9', '7', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '1', '4', '0', '5', '9', '7', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '6', '5', '6', '1', '7', '/', '3', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '6', '5', '6', '1', '7', '/', '3', '8', '0', '0', '0', '0', '0', '0'])]) :: ((.arr [.str (String.ofList ['2', '4', '2', '6', '5', '6', '2', '1', '/', '2', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '3', '4', '3', '7', '9', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '4', '5', '3', '1', '3', '7', '/', '1', '0', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '3', '5', '9', '3', '4', '7', '/', '1', '0', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '3', '5', '9', '3', '4', '7', '/', '2', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '3', '5', '9', '3', '4', '7', '/', '2', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '3', '5', '9', '3', '4', '7', '/', '2', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '0', '3', '1', '1', '3', '/', '5', '2', '0', '0', '0', '0', '0', '0'])]) :: (acc))
noncomputable def verticesArrayAcc00200 : List SourceJson := verticesChunk001Push00 verticesArrayAcc00100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertices_chunk_001_before"
  err.flush

theorem geometryChars00_vertices_chunk_001_prefix :
    (geometryChars00.drop 41072).take 472 = verticesChunk001Chars00 := by rfl

theorem geometryChars00_vertices_chunk_001_split :
    geometryChars00.drop 41072 = verticesChunk001Chars00 ++ geometryChars00.drop 41544 := by
  calc
    geometryChars00.drop 41072 =
        (geometryChars00.drop 41072).take 472 ++ (geometryChars00.drop 41072).drop 472 :=
      (List.take_append_drop 472 (geometryChars00.drop 41072)).symm
    _ = verticesChunk001Chars00 ++ (geometryChars00.drop 41072).drop 472 :=
      congrArg (fun p => p ++ (geometryChars00.drop 41072).drop 472) geometryChars00_vertices_chunk_001_prefix
    _ = verticesChunk001Chars00 ++ geometryChars00.drop 41544 := by rw [List.drop_drop]

theorem array_vertices_chunk_001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 52)
      (SourceJson.white (verticesChunk001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 50) (SourceJson.white tail)
        (verticesChunk001Push00 acc) := by rfl

theorem array_vertices_original_chunk_001 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 52)
      (SourceJson.white (geometryChars00.drop 41072)) acc =
      SourceJson.array (fuel + 50)
        (SourceJson.white (geometryChars00.drop 41544)) (verticesChunk001Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 52) (SourceJson.white s) acc)
      geometryChars00_vertices_chunk_001_split).trans
    (array_vertices_chunk_001 fuel (geometryChars00.drop 41544) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertices_chunk_001_complete"
  err.flush

noncomputable def verticesChunk002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '1', '0', '9', '3', '7', '1', '/', '5', '2', '2', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '0', '9', '4', '0', '1', '/', '1', '3', '0', '6', '2', '5', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '3', '2', '8', '1', '7', '3', '/', '1', '0', '4', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '9', '0', '5', '6', '9', '/', '5', '2', '2', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '9', '0', '5', '6', '9', '/', '1', '0', '4', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '9', '0', '5', '6', '9', '/', '1', '0', '4', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '9', '0', '5', '6', '9', '/', '1', '0', '4', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '4', '3', '7', '4', '3', '/', '1', '0', '4', '5', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '5', '6', '2', '4', '9', '/', '1', '2', '4', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '5', '2', '3', '6', '/', '7', '7', '8', '1', '2', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '5', '9', '3', '7', '9', '/', '8', '3', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '3', '4', '3', '6', '1', '/', '1', '2', '4', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '3', '4', '3', '6', '1', '/', '2', '4', '9', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '3', '4', '3', '6', '1', '/', '2', '4', '9', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '7', '4', '9', '9', '3', '/', '4', '1', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '7', '4', '9', '9', '3', '/', '4', '1', '5', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def verticesChunk002Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.str (String.ofList ['1', '4', '5', '6', '2', '4', '9', '/', '1', '2', '4', '5', '0', '0', '0', '0']), .str (String.ofList ['6', '5', '2', '3', '6', '/', '7', '7', '8', '1', '2', '5']), .str (String.ofList ['6', '5', '9', '3', '7', '9', '/', '8', '3', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '3', '4', '3', '6', '1', '/', '1', '2', '4', '5', '0', '0', '0', '0']), .str (String.ofList ['9', '3', '4', '3', '6', '1', '/', '2', '4', '9', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '3', '4', '3', '6', '1', '/', '2', '4', '9', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '7', '4', '9', '9', '3', '/', '4', '1', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '7', '4', '9', '9', '3', '/', '4', '1', '5', '0', '0', '0', '0', '0'])]) :: ((.arr [.str (String.ofList ['6', '1', '0', '9', '3', '7', '1', '/', '5', '2', '2', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '0', '9', '4', '0', '1', '/', '1', '3', '0', '6', '2', '5', '0', '0']), .str (String.ofList ['8', '3', '2', '8', '1', '7', '3', '/', '1', '0', '4', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '9', '0', '5', '6', '9', '/', '5', '2', '2', '5', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '9', '0', '5', '6', '9', '/', '1', '0', '4', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '9', '0', '5', '6', '9', '/', '1', '0', '4', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '9', '0', '5', '6', '9', '/', '1', '0', '4', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '3', '4', '3', '7', '4', '3', '/', '1', '0', '4', '5', '0', '0', '0', '0', '0'])]) :: (acc))
noncomputable def verticesArrayAcc00300 : List SourceJson := verticesChunk002Push00 verticesArrayAcc00200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertices_chunk_002_before"
  err.flush

theorem geometryChars00_vertices_chunk_002_prefix :
    (geometryChars00.drop 41544).take 456 = verticesChunk002Chars00 := by rfl

theorem geometryChars00_vertices_chunk_002_split :
    geometryChars00.drop 41544 = verticesChunk002Chars00 ++ geometryChars00.drop 42000 := by
  calc
    geometryChars00.drop 41544 =
        (geometryChars00.drop 41544).take 456 ++ (geometryChars00.drop 41544).drop 456 :=
      (List.take_append_drop 456 (geometryChars00.drop 41544)).symm
    _ = verticesChunk002Chars00 ++ (geometryChars00.drop 41544).drop 456 :=
      congrArg (fun p => p ++ (geometryChars00.drop 41544).drop 456) geometryChars00_vertices_chunk_002_prefix
    _ = verticesChunk002Chars00 ++ geometryChars00.drop 42000 := by rw [List.drop_drop]

theorem array_vertices_chunk_002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 50)
      (SourceJson.white (verticesChunk002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 48) (SourceJson.white tail)
        (verticesChunk002Push00 acc) := by rfl

theorem array_vertices_original_chunk_002 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 50)
      (SourceJson.white (geometryChars00.drop 41544)) acc =
      SourceJson.array (fuel + 48)
        (SourceJson.white (geometryChars00.drop 42000)) (verticesChunk002Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 50) (SourceJson.white s) acc)
      geometryChars00_vertices_chunk_002_split).trans
    (array_vertices_chunk_002 fuel (geometryChars00.drop 42000) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertices_chunk_002_complete"
  err.flush

noncomputable def verticesChunk003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '5', '1', '5', '6', '2', '1', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '9', '2', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '9', '/', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '5', '1', '5', '6', '2', '1', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '9', '2', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '9', '/', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def verticesChunk003Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.str (String.ofList ['3', '5', '1', '5', '6', '2', '1', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '9', '2', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '9', '/', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0'])]) :: ((.arr [.str (String.ofList ['3', '5', '1', '5', '6', '2', '1', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '9', '2', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '9', '/', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0'])]) :: (acc))
noncomputable def verticesArrayAcc00400 : List SourceJson := verticesChunk003Push00 verticesArrayAcc00300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertices_chunk_003_before"
  err.flush

theorem geometryChars00_vertices_chunk_003_prefix :
    (geometryChars00.drop 42000).take 453 = verticesChunk003Chars00 := by rfl

theorem geometryChars00_vertices_chunk_003_split :
    geometryChars00.drop 42000 = verticesChunk003Chars00 ++ geometryChars00.drop 42453 := by
  calc
    geometryChars00.drop 42000 =
        (geometryChars00.drop 42000).take 453 ++ (geometryChars00.drop 42000).drop 453 :=
      (List.take_append_drop 453 (geometryChars00.drop 42000)).symm
    _ = verticesChunk003Chars00 ++ (geometryChars00.drop 42000).drop 453 :=
      congrArg (fun p => p ++ (geometryChars00.drop 42000).drop 453) geometryChars00_vertices_chunk_003_prefix
    _ = verticesChunk003Chars00 ++ geometryChars00.drop 42453 := by rw [List.drop_drop]

theorem array_vertices_chunk_003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 48)
      (SourceJson.white (verticesChunk003Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 46) (SourceJson.white tail)
        (verticesChunk003Push00 acc) := by rfl

theorem array_vertices_original_chunk_003 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 48)
      (SourceJson.white (geometryChars00.drop 42000)) acc =
      SourceJson.array (fuel + 46)
        (SourceJson.white (geometryChars00.drop 42453)) (verticesChunk003Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 48) (SourceJson.white s) acc)
      geometryChars00_vertices_chunk_003_split).trans
    (array_vertices_chunk_003 fuel (geometryChars00.drop 42453) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertices_chunk_003_complete"
  err.flush

theorem vertices_array_through_block_000 (fuel : Nat) :
    SourceJson.array (fuel + 54)
      (SourceJson.white (geometryChars00.drop 40615)) [] =
      SourceJson.array (fuel + 46)
        (SourceJson.white (geometryChars00.drop 42453)) verticesArrayAcc00400 := by
  calc
    SourceJson.array (fuel + 54)
        (SourceJson.white (geometryChars00.drop 40615)) [] =
      SourceJson.array (fuel + 52)
        (SourceJson.white (geometryChars00.drop 41072)) verticesArrayAcc00100 :=
      array_vertices_original_chunk_000 fuel verticesArrayAcc00000
    _ =
      SourceJson.array (fuel + 50)
        (SourceJson.white (geometryChars00.drop 41544)) verticesArrayAcc00200 :=
      array_vertices_original_chunk_001 fuel verticesArrayAcc00100
    _ =
      SourceJson.array (fuel + 48)
        (SourceJson.white (geometryChars00.drop 42000)) verticesArrayAcc00300 :=
      array_vertices_original_chunk_002 fuel verticesArrayAcc00200
    _ =
      SourceJson.array (fuel + 46)
        (SourceJson.white (geometryChars00.drop 42453)) verticesArrayAcc00400 :=
      array_vertices_original_chunk_003 fuel verticesArrayAcc00300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertices_block_000_complete"
  err.flush

#print axioms geometryChars00_vertices_open_prefix
#print axioms geometryChars00_vertices_open_split
#print axioms value_vertices_open
#print axioms geometryChars00_vertices_chunk_000_prefix
#print axioms geometryChars00_vertices_chunk_000_split
#print axioms array_vertices_chunk_000
#print axioms array_vertices_original_chunk_000
#print axioms geometryChars00_vertices_chunk_001_prefix
#print axioms geometryChars00_vertices_chunk_001_split
#print axioms array_vertices_chunk_001
#print axioms array_vertices_original_chunk_001
#print axioms geometryChars00_vertices_chunk_002_prefix
#print axioms geometryChars00_vertices_chunk_002_split
#print axioms array_vertices_chunk_002
#print axioms array_vertices_original_chunk_002
#print axioms geometryChars00_vertices_chunk_003_prefix
#print axioms geometryChars00_vertices_chunk_003_split
#print axioms array_vertices_chunk_003
#print axioms array_vertices_original_chunk_003
#print axioms vertices_array_through_block_000

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
