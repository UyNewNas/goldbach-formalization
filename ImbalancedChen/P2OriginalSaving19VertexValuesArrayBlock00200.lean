import ImbalancedChen.P2OriginalSaving19VertexValuesArrayBlock00100

/-! Original vertex_values array block 2/6; small chunks with arbitrary tails and accumulators.
Exact original bytes are candidate data; the original reader equations below
are the Lean checks. No whole-file decide or replacement reader is used. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def vertexValuesChunk008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'R', '6', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'L', '3', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'B', '3', '"', ':', ' ', '"', '2', '7', '9', '1', '4', '1', '2', '5', '3', '/', '4', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'M', '8', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '"', ':', ' ', '"', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '7', '3', '4', '3', '8', '7', '/', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '7', '3', '4', '3', '8', '7', '/', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '5', '1', '5', '6', '2', '1', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '3', '9', '1', '0', '6', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '9', '/', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '7', '8', '1', '2', '9', '/', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '7', '8', '1', '2', '9', '/', '8', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def vertexValuesChunk008Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['R', '6'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['L', '3'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['B', '3'], .str (String.ofList ['2', '7', '9', '1', '4', '1', '2', '5', '3', '/', '4', '8', '0', '0', '0', '0', '0', '0', '0'])), (String.ofList ['M', '8'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['g', 'a', 'p'], .str (String.ofList ['0'])), (String.ofList ['f', 'a', 'c', 't', 'o', 'r', 's'], .arr [.str (String.ofList ['7', '7', '3', '4', '3', '8', '7', '/', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '7', '3', '4', '3', '8', '7', '/', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '1', '5', '6', '2', '1', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '3', '9', '1', '0', '6', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '9', '/', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '7', '8', '1', '2', '9', '/', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '7', '8', '1', '2', '9', '/', '8', '0', '0', '0', '0', '0', '0', '0'])])]) :: (acc)
noncomputable def vertexValuesArrayAcc00900 : List SourceJson := vertexValuesChunk008Push00 vertexValuesArrayAcc00800

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_chunk_008_before"
  err.flush

theorem geometryChars00_vertexValues_chunk_008_prefix :
    (geometryChars00.drop 50887).take 484 = vertexValuesChunk008Chars00 := by rfl

theorem geometryChars00_vertexValues_chunk_008_split :
    geometryChars00.drop 50887 = vertexValuesChunk008Chars00 ++ geometryChars00.drop 51371 := by
  calc
    geometryChars00.drop 50887 =
        (geometryChars00.drop 50887).take 484 ++ (geometryChars00.drop 50887).drop 484 :=
      (List.take_append_drop 484 (geometryChars00.drop 50887)).symm
    _ = vertexValuesChunk008Chars00 ++ (geometryChars00.drop 50887).drop 484 :=
      congrArg (fun p => p ++ (geometryChars00.drop 50887).drop 484) geometryChars00_vertexValues_chunk_008_prefix
    _ = vertexValuesChunk008Chars00 ++ geometryChars00.drop 51371 := by rw [List.drop_drop]

theorem array_vertexValues_chunk_008 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 55)
      (SourceJson.white (vertexValuesChunk008Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 54) (SourceJson.white tail)
        (vertexValuesChunk008Push00 acc) := by rfl

theorem array_vertexValues_original_chunk_008 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 55)
      (SourceJson.white (geometryChars00.drop 50887)) acc =
      SourceJson.array (fuel + 54)
        (SourceJson.white (geometryChars00.drop 51371)) (vertexValuesChunk008Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 55) (SourceJson.white s) acc)
      geometryChars00_vertexValues_chunk_008_split).trans
    (array_vertexValues_chunk_008 fuel (geometryChars00.drop 51371) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_chunk_008_complete"
  err.flush

noncomputable def vertexValuesChunk009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'R', '6', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'L', '3', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'B', '3', '"', ':', ' ', '"', '2', '0', '9', '7', '6', '6', '0', '3', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'M', '8', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '"', ':', ' ', '"', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '3', '9', '0', '6', '9', '3', '/', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '3', '9', '0', '6', '9', '3', '/', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '5', '1', '5', '6', '2', '1', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '7', '0', '3', '3', '9', '3', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '9', '/', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '3', '9', '0', '6', '9', '3', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def vertexValuesChunk009Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['R', '6'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['L', '3'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['B', '3'], .str (String.ofList ['2', '0', '9', '7', '6', '6', '0', '3', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0', '0'])), (String.ofList ['M', '8'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['g', 'a', 'p'], .str (String.ofList ['0'])), (String.ofList ['f', 'a', 'c', 't', 'o', 'r', 's'], .arr [.str (String.ofList ['5', '3', '9', '0', '6', '9', '3', '/', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '9', '0', '6', '9', '3', '/', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '1', '5', '6', '2', '1', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '7', '0', '3', '3', '9', '3', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '9', '/', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '9', '0', '6', '9', '3', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0'])])]) :: (acc)
noncomputable def vertexValuesArrayAcc01000 : List SourceJson := vertexValuesChunk009Push00 vertexValuesArrayAcc00900

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_chunk_009_before"
  err.flush

theorem geometryChars00_vertexValues_chunk_009_prefix :
    (geometryChars00.drop 51371).take 485 = vertexValuesChunk009Chars00 := by rfl

theorem geometryChars00_vertexValues_chunk_009_split :
    geometryChars00.drop 51371 = vertexValuesChunk009Chars00 ++ geometryChars00.drop 51856 := by
  calc
    geometryChars00.drop 51371 =
        (geometryChars00.drop 51371).take 485 ++ (geometryChars00.drop 51371).drop 485 :=
      (List.take_append_drop 485 (geometryChars00.drop 51371)).symm
    _ = vertexValuesChunk009Chars00 ++ (geometryChars00.drop 51371).drop 485 :=
      congrArg (fun p => p ++ (geometryChars00.drop 51371).drop 485) geometryChars00_vertexValues_chunk_009_prefix
    _ = vertexValuesChunk009Chars00 ++ geometryChars00.drop 51856 := by rw [List.drop_drop]

theorem array_vertexValues_chunk_009 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 54)
      (SourceJson.white (vertexValuesChunk009Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 53) (SourceJson.white tail)
        (vertexValuesChunk009Push00 acc) := by rfl

theorem array_vertexValues_original_chunk_009 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 54)
      (SourceJson.white (geometryChars00.drop 51371)) acc =
      SourceJson.array (fuel + 53)
        (SourceJson.white (geometryChars00.drop 51856)) (vertexValuesChunk009Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 54) (SourceJson.white s) acc)
      geometryChars00_vertexValues_chunk_009_split).trans
    (array_vertexValues_chunk_009 fuel (geometryChars00.drop 51856) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_chunk_009_complete"
  err.flush

noncomputable def vertexValuesChunk010Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'R', '6', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'L', '3', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'B', '3', '"', ':', ' ', '"', '1', '8', '1', '3', '5', '9', '8', '0', '3', '/', '3', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'M', '8', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '"', ':', ' ', '"', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '3', '6', '3', '/', '5', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '3', '6', '3', '/', '5', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '4', '4', '3', '7', '1', '/', '6', '2', '4', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '0', '9', '4', '1', '/', '2', '4', '3', '7', '5', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '5', '3', '1', '9', '3', '/', '5', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '8', '5', '9', '1', '6', '3', '/', '1', '5', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '3', '6', '6', '/', '6', '0', '9', '3', '7', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '4', '6', '7', '/', '1', '5', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '0', '3', '1', '2', '1', '/', '5', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '0', '3', '1', '2', '1', '/', '5', '2', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def vertexValuesChunk010Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['R', '6'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['L', '3'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['B', '3'], .str (String.ofList ['1', '8', '1', '3', '5', '9', '8', '0', '3', '/', '3', '1', '2', '0', '0', '0', '0', '0', '0'])), (String.ofList ['M', '8'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['g', 'a', 'p'], .str (String.ofList ['0'])), (String.ofList ['f', 'a', 'c', 't', 'o', 'r', 's'], .arr [.str (String.ofList ['5', '1', '0', '9', '3', '6', '3', '/', '5', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '0', '9', '3', '6', '3', '/', '5', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '4', '4', '3', '7', '1', '/', '6', '2', '4', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '0', '9', '4', '1', '/', '2', '4', '3', '7', '5', '0', '0']), .str (String.ofList ['3', '9', '5', '3', '1', '9', '3', '/', '5', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '8', '5', '9', '1', '6', '3', '/', '1', '5', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '3', '6', '6', '/', '6', '0', '9', '3', '7', '5']), .str (String.ofList ['5', '1', '0', '9', '4', '6', '7', '/', '1', '5', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '0', '3', '1', '2', '1', '/', '5', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '0', '3', '1', '2', '1', '/', '5', '2', '0', '0', '0', '0', '0', '0'])])]) :: (acc)
noncomputable def vertexValuesArrayAcc01100 : List SourceJson := vertexValuesChunk010Push00 vertexValuesArrayAcc01000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_chunk_010_before"
  err.flush

theorem geometryChars00_vertexValues_chunk_010_prefix :
    (geometryChars00.drop 51856).take 479 = vertexValuesChunk010Chars00 := by rfl

theorem geometryChars00_vertexValues_chunk_010_split :
    geometryChars00.drop 51856 = vertexValuesChunk010Chars00 ++ geometryChars00.drop 52335 := by
  calc
    geometryChars00.drop 51856 =
        (geometryChars00.drop 51856).take 479 ++ (geometryChars00.drop 51856).drop 479 :=
      (List.take_append_drop 479 (geometryChars00.drop 51856)).symm
    _ = vertexValuesChunk010Chars00 ++ (geometryChars00.drop 51856).drop 479 :=
      congrArg (fun p => p ++ (geometryChars00.drop 51856).drop 479) geometryChars00_vertexValues_chunk_010_prefix
    _ = vertexValuesChunk010Chars00 ++ geometryChars00.drop 52335 := by rw [List.drop_drop]

theorem array_vertexValues_chunk_010 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 53)
      (SourceJson.white (vertexValuesChunk010Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 52) (SourceJson.white tail)
        (vertexValuesChunk010Push00 acc) := by rfl

theorem array_vertexValues_original_chunk_010 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 53)
      (SourceJson.white (geometryChars00.drop 51856)) acc =
      SourceJson.array (fuel + 52)
        (SourceJson.white (geometryChars00.drop 52335)) (vertexValuesChunk010Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 53) (SourceJson.white s) acc)
      geometryChars00_vertexValues_chunk_010_split).trans
    (array_vertexValues_chunk_010 fuel (geometryChars00.drop 52335) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_chunk_010_complete"
  err.flush

noncomputable def vertexValuesChunk011Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'R', '6', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'L', '3', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'B', '3', '"', ':', ' ', '"', '1', '8', '1', '3', '5', '9', '8', '2', '7', '/', '3', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'M', '8', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '"', ':', ' ', '"', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '3', '3', '9', '/', '5', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '3', '3', '9', '/', '5', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '6', '0', '9', '2', '8', '3', '/', '1', '5', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '1', '8', '8', '3', '/', '4', '8', '7', '5', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '8', '5', '9', '5', '7', '1', '/', '1', '5', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '7', '1', '8', '3', '1', '/', '3', '1', '2', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '0', '6', '1', '9', '/', '3', '2', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '4', '4', '3', '/', '1', '5', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '4', '4', '3', '/', '1', '5', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '0', '3', '1', '1', '3', '/', '5', '2', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def vertexValuesChunk011Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['R', '6'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['L', '3'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['B', '3'], .str (String.ofList ['1', '8', '1', '3', '5', '9', '8', '2', '7', '/', '3', '1', '2', '0', '0', '0', '0', '0', '0'])), (String.ofList ['M', '8'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['g', 'a', 'p'], .str (String.ofList ['0'])), (String.ofList ['f', 'a', 'c', 't', 'o', 'r', 's'], .arr [.str (String.ofList ['5', '1', '0', '9', '3', '3', '9', '/', '5', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '0', '9', '3', '3', '9', '/', '5', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '6', '0', '9', '2', '8', '3', '/', '1', '5', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '1', '8', '8', '3', '/', '4', '8', '7', '5', '0', '0', '0']), .str (String.ofList ['1', '1', '8', '5', '9', '5', '7', '1', '/', '1', '5', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '7', '1', '8', '3', '1', '/', '3', '1', '2', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '0', '6', '1', '9', '/', '3', '2', '5', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '0', '9', '4', '4', '3', '/', '1', '5', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '0', '9', '4', '4', '3', '/', '1', '5', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '0', '3', '1', '1', '3', '/', '5', '2', '0', '0', '0', '0', '0', '0'])])]) :: (acc)
noncomputable def vertexValuesArrayAcc01200 : List SourceJson := vertexValuesChunk011Push00 vertexValuesArrayAcc01100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_chunk_011_before"
  err.flush

theorem geometryChars00_vertexValues_chunk_011_prefix :
    (geometryChars00.drop 52335).take 486 = vertexValuesChunk011Chars00 := by rfl

theorem geometryChars00_vertexValues_chunk_011_split :
    geometryChars00.drop 52335 = vertexValuesChunk011Chars00 ++ geometryChars00.drop 52821 := by
  calc
    geometryChars00.drop 52335 =
        (geometryChars00.drop 52335).take 486 ++ (geometryChars00.drop 52335).drop 486 :=
      (List.take_append_drop 486 (geometryChars00.drop 52335)).symm
    _ = vertexValuesChunk011Chars00 ++ (geometryChars00.drop 52335).drop 486 :=
      congrArg (fun p => p ++ (geometryChars00.drop 52335).drop 486) geometryChars00_vertexValues_chunk_011_prefix
    _ = vertexValuesChunk011Chars00 ++ geometryChars00.drop 52821 := by rw [List.drop_drop]

theorem array_vertexValues_chunk_011 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 52)
      (SourceJson.white (vertexValuesChunk011Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 51) (SourceJson.white tail)
        (vertexValuesChunk011Push00 acc) := by rfl

theorem array_vertexValues_original_chunk_011 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 52)
      (SourceJson.white (geometryChars00.drop 52335)) acc =
      SourceJson.array (fuel + 51)
        (SourceJson.white (geometryChars00.drop 52821)) (vertexValuesChunk011Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 52) (SourceJson.white s) acc)
      geometryChars00_vertexValues_chunk_011_split).trans
    (array_vertexValues_chunk_011 fuel (geometryChars00.drop 52821) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_chunk_011_complete"
  err.flush

theorem vertexValues_array_through_block_002 (fuel : Nat) :
    SourceJson.array (fuel + 63)
      (SourceJson.white (geometryChars00.drop 46997)) [] =
      SourceJson.array (fuel + 51)
        (SourceJson.white (geometryChars00.drop 52821)) vertexValuesArrayAcc01200 := by
  calc
    SourceJson.array (fuel + 63)
        (SourceJson.white (geometryChars00.drop 46997)) [] =
      SourceJson.array (fuel + 55)
        (SourceJson.white (geometryChars00.drop 50887)) vertexValuesArrayAcc00800 :=
      vertexValues_array_through_block_001 fuel
    _ =
      SourceJson.array (fuel + 54)
        (SourceJson.white (geometryChars00.drop 51371)) vertexValuesArrayAcc00900 :=
      array_vertexValues_original_chunk_008 fuel vertexValuesArrayAcc00800
    _ =
      SourceJson.array (fuel + 53)
        (SourceJson.white (geometryChars00.drop 51856)) vertexValuesArrayAcc01000 :=
      array_vertexValues_original_chunk_009 fuel vertexValuesArrayAcc00900
    _ =
      SourceJson.array (fuel + 52)
        (SourceJson.white (geometryChars00.drop 52335)) vertexValuesArrayAcc01100 :=
      array_vertexValues_original_chunk_010 fuel vertexValuesArrayAcc01000
    _ =
      SourceJson.array (fuel + 51)
        (SourceJson.white (geometryChars00.drop 52821)) vertexValuesArrayAcc01200 :=
      array_vertexValues_original_chunk_011 fuel vertexValuesArrayAcc01100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_block_002_complete"
  err.flush

#print axioms geometryChars00_vertexValues_chunk_008_prefix
#print axioms geometryChars00_vertexValues_chunk_008_split
#print axioms array_vertexValues_chunk_008
#print axioms array_vertexValues_original_chunk_008
#print axioms geometryChars00_vertexValues_chunk_009_prefix
#print axioms geometryChars00_vertexValues_chunk_009_split
#print axioms array_vertexValues_chunk_009
#print axioms array_vertexValues_original_chunk_009
#print axioms geometryChars00_vertexValues_chunk_010_prefix
#print axioms geometryChars00_vertexValues_chunk_010_split
#print axioms array_vertexValues_chunk_010
#print axioms array_vertexValues_original_chunk_010
#print axioms geometryChars00_vertexValues_chunk_011_prefix
#print axioms geometryChars00_vertexValues_chunk_011_split
#print axioms array_vertexValues_chunk_011
#print axioms array_vertexValues_original_chunk_011
#print axioms vertexValues_array_through_block_002

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
