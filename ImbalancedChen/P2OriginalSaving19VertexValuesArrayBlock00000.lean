import ImbalancedChen.P2OriginalSaving19VerticesField00

/-! Original vertex_values array block 0/6; small chunks with arbitrary tails and accumulators.
Exact original bytes are candidate data; the original reader equations below
are the Lean checks. No whole-file decide or replacement reader is used. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def vertexValuesOpenChars00 : List Char := ['[']
noncomputable def vertexValuesArrayAcc00000 : List SourceJson := []

theorem geometryChars00_vertexValues_open_prefix :
    (geometryChars00.drop 46996).take 1 = vertexValuesOpenChars00 := by rfl

theorem geometryChars00_vertexValues_open_split :
    geometryChars00.drop 46996 = vertexValuesOpenChars00 ++ geometryChars00.drop 46997 := by
  calc
    geometryChars00.drop 46996 =
        (geometryChars00.drop 46996).take 1 ++ (geometryChars00.drop 46996).drop 1 :=
      (List.take_append_drop 1 (geometryChars00.drop 46996)).symm
    _ = vertexValuesOpenChars00 ++ (geometryChars00.drop 46996).drop 1 :=
      congrArg (fun p => p ++ (geometryChars00.drop 46996).drop 1) geometryChars00_vertexValues_open_prefix
    _ = vertexValuesOpenChars00 ++ geometryChars00.drop 46997 := by rw [List.drop_drop]

theorem value_vertexValues_open (fuel : Nat) :
    SourceJson.value (fuel + 64) (geometryChars00.drop 46996) =
      SourceJson.array (fuel + 63)
        (SourceJson.white (geometryChars00.drop 46997)) [] := by
  calc
    SourceJson.value (fuel + 64) (geometryChars00.drop 46996) =
        SourceJson.value (fuel + 64)
          (vertexValuesOpenChars00 ++ geometryChars00.drop 46997) :=
      congrArg (SourceJson.value (fuel + 64)) geometryChars00_vertexValues_open_split
    _ = SourceJson.array (fuel + 63)
        (SourceJson.white (geometryChars00.drop 46997)) [] := by rfl

noncomputable def vertexValuesChunk000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'R', '6', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'L', '3', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'B', '3', '"', ':', ' ', '"', '8', '3', '5', '7', '8', '3', '6', '1', '/', '1', '4', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'M', '8', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '"', ':', ' ', '"', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '5', '4', '6', '9', '2', '7', '/', '1', '4', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '5', '7', '8', '5', '5', '3', '/', '1', '4', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '5', '7', '8', '1', '6', '9', '/', '1', '4', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '1', '5', '5', '5', '7', '/', '2', '8', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '7', '9', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '7', '9', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '7', '9', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def vertexValuesChunk000Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['R', '6'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['L', '3'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['B', '3'], .str (String.ofList ['8', '3', '5', '7', '8', '3', '6', '1', '/', '1', '4', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['M', '8'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['g', 'a', 'p'], .str (String.ofList ['0'])), (String.ofList ['f', 'a', 'c', 't', 'o', 'r', 's'], .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '5', '4', '6', '9', '2', '7', '/', '1', '4', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '5', '7', '8', '5', '5', '3', '/', '1', '4', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '5', '7', '8', '1', '6', '9', '/', '1', '4', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '1', '5', '5', '5', '7', '/', '2', '8', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '7', '9', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '7', '9', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '7', '9', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '7', '2', '0', '0', '0', '0', '0', '0'])])]) :: (acc)
noncomputable def vertexValuesArrayAcc00100 : List SourceJson := vertexValuesChunk000Push00 vertexValuesArrayAcc00000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_chunk_000_before"
  err.flush

theorem geometryChars00_vertexValues_chunk_000_prefix :
    (geometryChars00.drop 46997).take 489 = vertexValuesChunk000Chars00 := by rfl

theorem geometryChars00_vertexValues_chunk_000_split :
    geometryChars00.drop 46997 = vertexValuesChunk000Chars00 ++ geometryChars00.drop 47486 := by
  calc
    geometryChars00.drop 46997 =
        (geometryChars00.drop 46997).take 489 ++ (geometryChars00.drop 46997).drop 489 :=
      (List.take_append_drop 489 (geometryChars00.drop 46997)).symm
    _ = vertexValuesChunk000Chars00 ++ (geometryChars00.drop 46997).drop 489 :=
      congrArg (fun p => p ++ (geometryChars00.drop 46997).drop 489) geometryChars00_vertexValues_chunk_000_prefix
    _ = vertexValuesChunk000Chars00 ++ geometryChars00.drop 47486 := by rw [List.drop_drop]

theorem array_vertexValues_chunk_000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 63)
      (SourceJson.white (vertexValuesChunk000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 62) (SourceJson.white tail)
        (vertexValuesChunk000Push00 acc) := by rfl

theorem array_vertexValues_original_chunk_000 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 63)
      (SourceJson.white (geometryChars00.drop 46997)) acc =
      SourceJson.array (fuel + 62)
        (SourceJson.white (geometryChars00.drop 47486)) (vertexValuesChunk000Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 63) (SourceJson.white s) acc)
      geometryChars00_vertexValues_chunk_000_split).trans
    (array_vertexValues_chunk_000 fuel (geometryChars00.drop 47486) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_chunk_000_complete"
  err.flush

noncomputable def vertexValuesChunk001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'R', '6', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'L', '3', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'B', '3', '"', ':', ' ', '"', '2', '7', '8', '5', '9', '4', '5', '1', '/', '4', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'M', '8', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '"', ':', ' ', '"', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '0', '3', '1', '2', '9', '/', '9', '6', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '7', '3', '0', '1', '/', '3', '2', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '5', '9', '3', '8', '7', '/', '4', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '5', '9', '2', '5', '9', '/', '4', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '6', '0', '4', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '6', '0', '4', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def vertexValuesChunk001Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['R', '6'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['L', '3'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['B', '3'], .str (String.ofList ['2', '7', '8', '5', '9', '4', '5', '1', '/', '4', '8', '0', '0', '0', '0', '0', '0'])), (String.ofList ['M', '8'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['g', 'a', 'p'], .str (String.ofList ['0'])), (String.ofList ['f', 'a', 'c', 't', 'o', 'r', 's'], .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '0', '3', '1', '2', '9', '/', '9', '6', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '7', '3', '0', '1', '/', '3', '2', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '5', '9', '3', '8', '7', '/', '4', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '5', '9', '2', '5', '9', '/', '4', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '6', '0', '4', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '6', '0', '4', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0'])])]) :: (acc)
noncomputable def vertexValuesArrayAcc00200 : List SourceJson := vertexValuesChunk001Push00 vertexValuesArrayAcc00100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_chunk_001_before"
  err.flush

theorem geometryChars00_vertexValues_chunk_001_prefix :
    (geometryChars00.drop 47486).take 469 = vertexValuesChunk001Chars00 := by rfl

theorem geometryChars00_vertexValues_chunk_001_split :
    geometryChars00.drop 47486 = vertexValuesChunk001Chars00 ++ geometryChars00.drop 47955 := by
  calc
    geometryChars00.drop 47486 =
        (geometryChars00.drop 47486).take 469 ++ (geometryChars00.drop 47486).drop 469 :=
      (List.take_append_drop 469 (geometryChars00.drop 47486)).symm
    _ = vertexValuesChunk001Chars00 ++ (geometryChars00.drop 47486).drop 469 :=
      congrArg (fun p => p ++ (geometryChars00.drop 47486).drop 469) geometryChars00_vertexValues_chunk_001_prefix
    _ = vertexValuesChunk001Chars00 ++ geometryChars00.drop 47955 := by rw [List.drop_drop]

theorem array_vertexValues_chunk_001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 62)
      (SourceJson.white (vertexValuesChunk001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 61) (SourceJson.white tail)
        (vertexValuesChunk001Push00 acc) := by rfl

theorem array_vertexValues_original_chunk_001 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 62)
      (SourceJson.white (geometryChars00.drop 47486)) acc =
      SourceJson.array (fuel + 61)
        (SourceJson.white (geometryChars00.drop 47955)) (vertexValuesChunk001Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 62) (SourceJson.white s) acc)
      geometryChars00_vertexValues_chunk_001_split).trans
    (array_vertexValues_chunk_001 fuel (geometryChars00.drop 47955) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_chunk_001_complete"
  err.flush

noncomputable def vertexValuesChunk002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'R', '6', '"', ':', ' ', '"', '4', '9', '3', '9', '6', '8', '6', '3', '/', '8', '3', '2', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'L', '3', '"', ':', ' ', '"', '4', '9', '3', '9', '6', '8', '6', '3', '/', '8', '3', '2', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'B', '3', '"', ':', ' ', '"', '1', '9', '0', '6', '2', '5', '1', '/', '3', '2', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'M', '8', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '6', '4', '0', '2', '6', '9', '/', '4', '1', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '2', '3', '4', '4', '4', '3', '/', '4', '1', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '3', '3', '9', '/', '5', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '2', '6', '5', '6', '2', '1', '/', '2', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '4', '3', '7', '9', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '4', '5', '3', '1', '3', '7', '/', '1', '0', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '5', '9', '3', '4', '7', '/', '1', '0', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '5', '9', '3', '4', '7', '/', '2', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '5', '9', '3', '4', '7', '/', '2', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '5', '9', '3', '4', '7', '/', '2', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '0', '3', '1', '1', '3', '/', '5', '2', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def vertexValuesChunk002Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['R', '6'], .str (String.ofList ['4', '9', '3', '9', '6', '8', '6', '3', '/', '8', '3', '2', '0', '0', '0', '0', '0'])), (String.ofList ['L', '3'], .str (String.ofList ['4', '9', '3', '9', '6', '8', '6', '3', '/', '8', '3', '2', '0', '0', '0', '0', '0'])), (String.ofList ['B', '3'], .str (String.ofList ['1', '9', '0', '6', '2', '5', '1', '/', '3', '2', '5', '0', '0', '0', '0'])), (String.ofList ['M', '8'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['g', 'a', 'p'], .str (String.ofList ['1', '6', '4', '0', '2', '6', '9', '/', '4', '1', '6', '0', '0', '0', '0', '0', '0'])), (String.ofList ['f', 'a', 'c', 't', 'o', 'r', 's'], .arr [.str (String.ofList ['3', '9', '2', '3', '4', '4', '4', '3', '/', '4', '1', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '0', '9', '3', '3', '9', '/', '5', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '2', '6', '5', '6', '2', '1', '/', '2', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '3', '4', '3', '7', '9', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '4', '5', '3', '1', '3', '7', '/', '1', '0', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '3', '5', '9', '3', '4', '7', '/', '1', '0', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '3', '5', '9', '3', '4', '7', '/', '2', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '3', '5', '9', '3', '4', '7', '/', '2', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '3', '5', '9', '3', '4', '7', '/', '2', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '0', '3', '1', '1', '3', '/', '5', '2', '0', '0', '0', '0', '0', '0'])])]) :: (acc)
noncomputable def vertexValuesArrayAcc00300 : List SourceJson := vertexValuesChunk002Push00 vertexValuesArrayAcc00200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_chunk_002_before"
  err.flush

theorem geometryChars00_vertexValues_chunk_002_prefix :
    (geometryChars00.drop 47955).take 507 = vertexValuesChunk002Chars00 := by rfl

theorem geometryChars00_vertexValues_chunk_002_split :
    geometryChars00.drop 47955 = vertexValuesChunk002Chars00 ++ geometryChars00.drop 48462 := by
  calc
    geometryChars00.drop 47955 =
        (geometryChars00.drop 47955).take 507 ++ (geometryChars00.drop 47955).drop 507 :=
      (List.take_append_drop 507 (geometryChars00.drop 47955)).symm
    _ = vertexValuesChunk002Chars00 ++ (geometryChars00.drop 47955).drop 507 :=
      congrArg (fun p => p ++ (geometryChars00.drop 47955).drop 507) geometryChars00_vertexValues_chunk_002_prefix
    _ = vertexValuesChunk002Chars00 ++ geometryChars00.drop 48462 := by rw [List.drop_drop]

theorem array_vertexValues_chunk_002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 61)
      (SourceJson.white (vertexValuesChunk002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 60) (SourceJson.white tail)
        (vertexValuesChunk002Push00 acc) := by rfl

theorem array_vertexValues_original_chunk_002 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 61)
      (SourceJson.white (geometryChars00.drop 47955)) acc =
      SourceJson.array (fuel + 60)
        (SourceJson.white (geometryChars00.drop 48462)) (vertexValuesChunk002Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 61) (SourceJson.white s) acc)
      geometryChars00_vertexValues_chunk_002_split).trans
    (array_vertexValues_chunk_002 fuel (geometryChars00.drop 48462) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_chunk_002_complete"
  err.flush

noncomputable def vertexValuesChunk003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'R', '6', '"', ':', ' ', '"', '1', '8', '0', '5', '9', '3', '7', '1', '/', '3', '0', '4', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'L', '3', '"', ':', ' ', '"', '1', '8', '0', '5', '9', '3', '7', '1', '/', '3', '0', '4', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'B', '3', '"', ':', ' ', '"', '3', '3', '3', '9', '0', '6', '4', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'M', '8', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '"', ':', ' ', '"', '5', '4', '6', '7', '4', '3', '/', '1', '5', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '6', '4', '0', '6', '6', '1', '/', '1', '5', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '9', '6', '8', '5', '1', '/', '3', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '6', '0', '9', '3', '7', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '3', '2', '8', '1', '7', '7', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '7', '8', '1', '2', '9', '/', '3', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '1', '4', '0', '5', '9', '7', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '1', '4', '0', '5', '9', '7', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '1', '4', '0', '5', '9', '7', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '6', '5', '6', '1', '7', '/', '3', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '6', '5', '6', '1', '7', '/', '3', '8', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def vertexValuesChunk003Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['R', '6'], .str (String.ofList ['1', '8', '0', '5', '9', '3', '7', '1', '/', '3', '0', '4', '0', '0', '0', '0', '0'])), (String.ofList ['L', '3'], .str (String.ofList ['1', '8', '0', '5', '9', '3', '7', '1', '/', '3', '0', '4', '0', '0', '0', '0', '0'])), (String.ofList ['B', '3'], .str (String.ofList ['3', '3', '3', '9', '0', '6', '4', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0'])), (String.ofList ['M', '8'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['g', 'a', 'p'], .str (String.ofList ['5', '4', '6', '7', '4', '3', '/', '1', '5', '2', '0', '0', '0', '0', '0', '0'])), (String.ofList ['f', 'a', 'c', 't', 'o', 'r', 's'], .arr [.str (String.ofList ['1', '4', '6', '4', '0', '6', '6', '1', '/', '1', '5', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '9', '6', '8', '5', '1', '/', '3', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '6', '0', '9', '3', '7', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '3', '2', '8', '1', '7', '7', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '0', '7', '8', '1', '2', '9', '/', '3', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '1', '4', '0', '5', '9', '7', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '1', '4', '0', '5', '9', '7', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '1', '4', '0', '5', '9', '7', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '6', '5', '6', '1', '7', '/', '3', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '6', '5', '6', '1', '7', '/', '3', '8', '0', '0', '0', '0', '0', '0'])])]) :: (acc)
noncomputable def vertexValuesArrayAcc00400 : List SourceJson := vertexValuesChunk003Push00 vertexValuesArrayAcc00300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_chunk_003_before"
  err.flush

theorem geometryChars00_vertexValues_chunk_003_prefix :
    (geometryChars00.drop 48462).take 510 = vertexValuesChunk003Chars00 := by rfl

theorem geometryChars00_vertexValues_chunk_003_split :
    geometryChars00.drop 48462 = vertexValuesChunk003Chars00 ++ geometryChars00.drop 48972 := by
  calc
    geometryChars00.drop 48462 =
        (geometryChars00.drop 48462).take 510 ++ (geometryChars00.drop 48462).drop 510 :=
      (List.take_append_drop 510 (geometryChars00.drop 48462)).symm
    _ = vertexValuesChunk003Chars00 ++ (geometryChars00.drop 48462).drop 510 :=
      congrArg (fun p => p ++ (geometryChars00.drop 48462).drop 510) geometryChars00_vertexValues_chunk_003_prefix
    _ = vertexValuesChunk003Chars00 ++ geometryChars00.drop 48972 := by rw [List.drop_drop]

theorem array_vertexValues_chunk_003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 60)
      (SourceJson.white (vertexValuesChunk003Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 59) (SourceJson.white tail)
        (vertexValuesChunk003Push00 acc) := by rfl

theorem array_vertexValues_original_chunk_003 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 60)
      (SourceJson.white (geometryChars00.drop 48462)) acc =
      SourceJson.array (fuel + 59)
        (SourceJson.white (geometryChars00.drop 48972)) (vertexValuesChunk003Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 60) (SourceJson.white s) acc)
      geometryChars00_vertexValues_chunk_003_split).trans
    (array_vertexValues_chunk_003 fuel (geometryChars00.drop 48972) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_chunk_003_complete"
  err.flush

theorem vertexValues_array_through_block_000 (fuel : Nat) :
    SourceJson.array (fuel + 63)
      (SourceJson.white (geometryChars00.drop 46997)) [] =
      SourceJson.array (fuel + 59)
        (SourceJson.white (geometryChars00.drop 48972)) vertexValuesArrayAcc00400 := by
  calc
    SourceJson.array (fuel + 63)
        (SourceJson.white (geometryChars00.drop 46997)) [] =
      SourceJson.array (fuel + 62)
        (SourceJson.white (geometryChars00.drop 47486)) vertexValuesArrayAcc00100 :=
      array_vertexValues_original_chunk_000 fuel vertexValuesArrayAcc00000
    _ =
      SourceJson.array (fuel + 61)
        (SourceJson.white (geometryChars00.drop 47955)) vertexValuesArrayAcc00200 :=
      array_vertexValues_original_chunk_001 fuel vertexValuesArrayAcc00100
    _ =
      SourceJson.array (fuel + 60)
        (SourceJson.white (geometryChars00.drop 48462)) vertexValuesArrayAcc00300 :=
      array_vertexValues_original_chunk_002 fuel vertexValuesArrayAcc00200
    _ =
      SourceJson.array (fuel + 59)
        (SourceJson.white (geometryChars00.drop 48972)) vertexValuesArrayAcc00400 :=
      array_vertexValues_original_chunk_003 fuel vertexValuesArrayAcc00300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_block_000_complete"
  err.flush

#print axioms geometryChars00_vertexValues_open_prefix
#print axioms geometryChars00_vertexValues_open_split
#print axioms value_vertexValues_open
#print axioms geometryChars00_vertexValues_chunk_000_prefix
#print axioms geometryChars00_vertexValues_chunk_000_split
#print axioms array_vertexValues_chunk_000
#print axioms array_vertexValues_original_chunk_000
#print axioms geometryChars00_vertexValues_chunk_001_prefix
#print axioms geometryChars00_vertexValues_chunk_001_split
#print axioms array_vertexValues_chunk_001
#print axioms array_vertexValues_original_chunk_001
#print axioms geometryChars00_vertexValues_chunk_002_prefix
#print axioms geometryChars00_vertexValues_chunk_002_split
#print axioms array_vertexValues_chunk_002
#print axioms array_vertexValues_original_chunk_002
#print axioms geometryChars00_vertexValues_chunk_003_prefix
#print axioms geometryChars00_vertexValues_chunk_003_split
#print axioms array_vertexValues_chunk_003
#print axioms array_vertexValues_original_chunk_003
#print axioms vertexValues_array_through_block_000

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
