import ImbalancedChen.P2OriginalSaving19VertexValuesArrayBlock00500

/-! Original vertex_values array block 6/6; small chunks with arbitrary tails and accumulators.
Exact original bytes are candidate data; the original reader equations below
are the Lean checks. No whole-file decide or replacement reader is used. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def vertexValuesChunk024Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'R', '6', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'L', '3', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'B', '3', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'M', '8', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '"', ':', ' ', '"', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '4', '3', '7', '9', '/', '2', '4', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '4', '3', '7', '9', '/', '2', '4', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '6', '6', '5', '5', '9', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '6', '5', '5', '8', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '9', '/', '1', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '6', '8', '7', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '2', '1', '9', '1', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '4', '3', '7', '9', '/', '7', '2', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '4', '3', '7', '9', '/', '7', '2', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def vertexValuesChunk024Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['R', '6'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['L', '3'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['B', '3'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['M', '8'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['g', 'a', 'p'], .str (String.ofList ['0'])), (String.ofList ['f', 'a', 'c', 't', 'o', 'r', 's'], .arr [.str (String.ofList ['2', '0', '4', '3', '7', '9', '/', '2', '4', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '4', '3', '7', '9', '/', '2', '4', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '3', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '6', '6', '5', '5', '9', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '3', '6', '5', '5', '8', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '1', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '6', '8', '7', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '2', '1', '9', '1', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '4', '3', '7', '9', '/', '7', '2', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '4', '3', '7', '9', '/', '7', '2', '0', '0', '0', '0', '0'])])]) :: (acc)
noncomputable def vertexValuesArrayAcc02500 : List SourceJson := vertexValuesChunk024Push00 vertexValuesArrayAcc02400

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_chunk_024_before"
  err.flush

theorem geometryChars00_vertexValues_chunk_024_prefix :
    (geometryChars00.drop 58540).take 468 = vertexValuesChunk024Chars00 := by rfl

theorem geometryChars00_vertexValues_chunk_024_split :
    geometryChars00.drop 58540 = vertexValuesChunk024Chars00 ++ geometryChars00.drop 59008 := by
  calc
    geometryChars00.drop 58540 =
        (geometryChars00.drop 58540).take 468 ++ (geometryChars00.drop 58540).drop 468 :=
      (List.take_append_drop 468 (geometryChars00.drop 58540)).symm
    _ = vertexValuesChunk024Chars00 ++ (geometryChars00.drop 58540).drop 468 :=
      congrArg (fun p => p ++ (geometryChars00.drop 58540).drop 468) geometryChars00_vertexValues_chunk_024_prefix
    _ = vertexValuesChunk024Chars00 ++ geometryChars00.drop 59008 := by rw [List.drop_drop]

theorem array_vertexValues_chunk_024 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 39)
      (SourceJson.white (vertexValuesChunk024Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 38) (SourceJson.white tail)
        (vertexValuesChunk024Push00 acc) := by rfl

theorem array_vertexValues_original_chunk_024 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 39)
      (SourceJson.white (geometryChars00.drop 58540)) acc =
      SourceJson.array (fuel + 38)
        (SourceJson.white (geometryChars00.drop 59008)) (vertexValuesChunk024Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 39) (SourceJson.white s) acc)
      geometryChars00_vertexValues_chunk_024_split).trans
    (array_vertexValues_chunk_024 fuel (geometryChars00.drop 59008) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_chunk_024_complete"
  err.flush

noncomputable def vertexValuesChunk025Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'R', '6', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'L', '3', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'B', '3', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'M', '8', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '"', ':', ' ', '"', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '4', '5', '1', '/', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '4', '5', '1', '/', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '2', '8', '0', '0', '9', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '8', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '9', '/', '1', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '0', '3', '0', '7', '3', '/', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '5', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '5', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '4', '5', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def vertexValuesChunk025Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['R', '6'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['L', '3'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['B', '3'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['M', '8'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['g', 'a', 'p'], .str (String.ofList ['0'])), (String.ofList ['f', 'a', 'c', 't', 'o', 'r', 's'], .arr [.str (String.ofList ['5', '1', '0', '9', '4', '5', '1', '/', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '0', '9', '4', '5', '1', '/', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '3', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '8', '0', '0', '9', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '8', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '1', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '0', '3', '0', '7', '3', '/', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '0', '9', '5', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '0', '9', '5', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '0', '9', '4', '5', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0'])])]) :: (acc)
noncomputable def vertexValuesArrayAcc02600 : List SourceJson := vertexValuesChunk025Push00 vertexValuesArrayAcc02500

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_chunk_025_before"
  err.flush

theorem geometryChars00_vertexValues_chunk_025_prefix :
    (geometryChars00.drop 59008).take 485 = vertexValuesChunk025Chars00 := by rfl

theorem geometryChars00_vertexValues_chunk_025_split :
    geometryChars00.drop 59008 = vertexValuesChunk025Chars00 ++ geometryChars00.drop 59493 := by
  calc
    geometryChars00.drop 59008 =
        (geometryChars00.drop 59008).take 485 ++ (geometryChars00.drop 59008).drop 485 :=
      (List.take_append_drop 485 (geometryChars00.drop 59008)).symm
    _ = vertexValuesChunk025Chars00 ++ (geometryChars00.drop 59008).drop 485 :=
      congrArg (fun p => p ++ (geometryChars00.drop 59008).drop 485) geometryChars00_vertexValues_chunk_025_prefix
    _ = vertexValuesChunk025Chars00 ++ geometryChars00.drop 59493 := by rw [List.drop_drop]

theorem array_vertexValues_chunk_025 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 38)
      (SourceJson.white (vertexValuesChunk025Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 37) (SourceJson.white tail)
        (vertexValuesChunk025Push00 acc) := by rfl

theorem array_vertexValues_original_chunk_025 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 38)
      (SourceJson.white (geometryChars00.drop 59008)) acc =
      SourceJson.array (fuel + 37)
        (SourceJson.white (geometryChars00.drop 59493)) (vertexValuesChunk025Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 38) (SourceJson.white s) acc)
      geometryChars00_vertexValues_chunk_025_split).trans
    (array_vertexValues_chunk_025 fuel (geometryChars00.drop 59493) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_chunk_025_complete"
  err.flush

noncomputable def vertexValuesChunk026Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'R', '6', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'L', '3', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'B', '3', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'M', '8', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '"', ':', ' ', '"', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '9', '6', '8', '7', '9', '/', '5', '6', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '9', '6', '8', '7', '9', '/', '5', '6', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '7', '1', '8', '5', '9', '/', '4', '2', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '9', '5', '2', '9', '5', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '4', '5', '3', '1', '2', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '4', '5', '1', '/', '4', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '4', '5', '1', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '4', '5', '1', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '9', '6', '8', '7', '9', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '9', '6', '8', '7', '9', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def vertexValuesChunk026Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['R', '6'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['L', '3'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['B', '3'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['M', '8'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['g', 'a', 'p'], .str (String.ofList ['0'])), (String.ofList ['f', 'a', 'c', 't', 'o', 'r', 's'], .arr [.str (String.ofList ['4', '9', '6', '8', '7', '9', '/', '5', '6', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '9', '6', '8', '7', '9', '/', '5', '6', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '7', '1', '8', '5', '9', '/', '4', '2', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '9', '5', '2', '9', '5', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '4', '5', '3', '1', '2', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '4', '5', '1', '/', '4', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '4', '5', '1', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '4', '5', '1', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '9', '6', '8', '7', '9', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '9', '6', '8', '7', '9', '/', '1', '6', '8', '0', '0', '0', '0', '0'])])]) :: (acc)
noncomputable def vertexValuesArrayAcc02700 : List SourceJson := vertexValuesChunk026Push00 vertexValuesArrayAcc02600

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_chunk_026_before"
  err.flush

theorem geometryChars00_vertexValues_chunk_026_prefix :
    (geometryChars00.drop 59493).take 472 = vertexValuesChunk026Chars00 := by rfl

theorem geometryChars00_vertexValues_chunk_026_split :
    geometryChars00.drop 59493 = vertexValuesChunk026Chars00 ++ geometryChars00.drop 59965 := by
  calc
    geometryChars00.drop 59493 =
        (geometryChars00.drop 59493).take 472 ++ (geometryChars00.drop 59493).drop 472 :=
      (List.take_append_drop 472 (geometryChars00.drop 59493)).symm
    _ = vertexValuesChunk026Chars00 ++ (geometryChars00.drop 59493).drop 472 :=
      congrArg (fun p => p ++ (geometryChars00.drop 59493).drop 472) geometryChars00_vertexValues_chunk_026_prefix
    _ = vertexValuesChunk026Chars00 ++ geometryChars00.drop 59965 := by rw [List.drop_drop]

theorem array_vertexValues_chunk_026 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 37)
      (SourceJson.white (vertexValuesChunk026Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 36) (SourceJson.white tail)
        (vertexValuesChunk026Push00 acc) := by rfl

theorem array_vertexValues_original_chunk_026 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 37)
      (SourceJson.white (geometryChars00.drop 59493)) acc =
      SourceJson.array (fuel + 36)
        (SourceJson.white (geometryChars00.drop 59965)) (vertexValuesChunk026Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 37) (SourceJson.white s) acc)
      geometryChars00_vertexValues_chunk_026_split).trans
    (array_vertexValues_chunk_026 fuel (geometryChars00.drop 59965) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_chunk_026_complete"
  err.flush

noncomputable def vertexValuesChunk027Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'R', '6', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'L', '3', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'B', '3', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'M', '8', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '"', ':', ' ', '"', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '8', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '8', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '9', '5', '2', '9', '7', '7', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '9', '0', '6', '2', '1', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '4', '4', '3', '/', '4', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '4', '4', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '4', '4', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '4', '4', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '2', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', '}', '\r', '\n', ' ', ' ', ']']
noncomputable def vertexValuesChunk027Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['R', '6'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['L', '3'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['B', '3'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['M', '8'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['g', 'a', 'p'], .str (String.ofList ['0'])), (String.ofList ['f', 'a', 'c', 't', 'o', 'r', 's'], .arr [.str (String.ofList ['2', '4', '8', '4', '3', '8', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '8', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '9', '5', '2', '9', '7', '7', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '9', '0', '6', '2', '1', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '4', '4', '3', '/', '4', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '4', '4', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '4', '4', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '4', '4', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '2', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0'])])]) :: (acc)
noncomputable def vertexValuesArrayAcc02800 : List SourceJson := vertexValuesChunk027Push00 vertexValuesArrayAcc02700

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_chunk_027_before"
  err.flush

theorem geometryChars00_vertexValues_chunk_027_prefix :
    (geometryChars00.drop 59965).take 483 = vertexValuesChunk027Chars00 := by rfl

theorem geometryChars00_vertexValues_chunk_027_split :
    geometryChars00.drop 59965 = vertexValuesChunk027Chars00 ++ geometryChars00.drop 60448 := by
  calc
    geometryChars00.drop 59965 =
        (geometryChars00.drop 59965).take 483 ++ (geometryChars00.drop 59965).drop 483 :=
      (List.take_append_drop 483 (geometryChars00.drop 59965)).symm
    _ = vertexValuesChunk027Chars00 ++ (geometryChars00.drop 59965).drop 483 :=
      congrArg (fun p => p ++ (geometryChars00.drop 59965).drop 483) geometryChars00_vertexValues_chunk_027_prefix
    _ = vertexValuesChunk027Chars00 ++ geometryChars00.drop 60448 := by rw [List.drop_drop]

theorem array_vertexValues_chunk_027 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 36)
      (SourceJson.white (vertexValuesChunk027Chars00 ++ tail)) acc =
      .ok (.arr ((vertexValuesChunk027Push00 acc).reverse), tail) := by rfl

theorem array_vertexValues_original_chunk_027 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 36)
      (SourceJson.white (geometryChars00.drop 59965)) acc =
      .ok (.arr ((vertexValuesChunk027Push00 acc).reverse), geometryChars00.drop 60448) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 36) (SourceJson.white s) acc)
      geometryChars00_vertexValues_chunk_027_split).trans
    (array_vertexValues_chunk_027 fuel (geometryChars00.drop 60448) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_chunk_027_complete"
  err.flush

noncomputable def vertexValuesArrayValue00 : SourceJson := .arr (vertexValuesArrayAcc02800.reverse)

theorem vertexValues_array_through_block_006 (fuel : Nat) :
    SourceJson.array (fuel + 63)
      (SourceJson.white (geometryChars00.drop 46997)) [] =
      .ok (vertexValuesArrayValue00, geometryChars00.drop 60448) := by
  calc
    SourceJson.array (fuel + 63)
        (SourceJson.white (geometryChars00.drop 46997)) [] =
      SourceJson.array (fuel + 39)
        (SourceJson.white (geometryChars00.drop 58540)) vertexValuesArrayAcc02400 :=
      vertexValues_array_through_block_005 fuel
    _ =
      SourceJson.array (fuel + 38)
        (SourceJson.white (geometryChars00.drop 59008)) vertexValuesArrayAcc02500 :=
      array_vertexValues_original_chunk_024 fuel vertexValuesArrayAcc02400
    _ =
      SourceJson.array (fuel + 37)
        (SourceJson.white (geometryChars00.drop 59493)) vertexValuesArrayAcc02600 :=
      array_vertexValues_original_chunk_025 fuel vertexValuesArrayAcc02500
    _ =
      SourceJson.array (fuel + 36)
        (SourceJson.white (geometryChars00.drop 59965)) vertexValuesArrayAcc02700 :=
      array_vertexValues_original_chunk_026 fuel vertexValuesArrayAcc02600
    _ =
      .ok (vertexValuesArrayValue00, geometryChars00.drop 60448) :=
      array_vertexValues_original_chunk_027 fuel vertexValuesArrayAcc02700

theorem value_vertexValues_original (fuel : Nat) :
    SourceJson.value (fuel + 64) (geometryChars00.drop 46996) =
      .ok (vertexValuesArrayValue00, geometryChars00.drop 60448) := by
  exact (value_vertexValues_open fuel).trans (vertexValues_array_through_block_006 fuel)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_block_006_complete"
  err.flush

#print axioms geometryChars00_vertexValues_chunk_024_prefix
#print axioms geometryChars00_vertexValues_chunk_024_split
#print axioms array_vertexValues_chunk_024
#print axioms array_vertexValues_original_chunk_024
#print axioms geometryChars00_vertexValues_chunk_025_prefix
#print axioms geometryChars00_vertexValues_chunk_025_split
#print axioms array_vertexValues_chunk_025
#print axioms array_vertexValues_original_chunk_025
#print axioms geometryChars00_vertexValues_chunk_026_prefix
#print axioms geometryChars00_vertexValues_chunk_026_split
#print axioms array_vertexValues_chunk_026
#print axioms array_vertexValues_original_chunk_026
#print axioms geometryChars00_vertexValues_chunk_027_prefix
#print axioms geometryChars00_vertexValues_chunk_027_split
#print axioms array_vertexValues_chunk_027
#print axioms array_vertexValues_original_chunk_027
#print axioms vertexValues_array_through_block_006
#print axioms value_vertexValues_original

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
