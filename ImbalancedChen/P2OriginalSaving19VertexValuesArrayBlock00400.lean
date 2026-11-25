import ImbalancedChen.P2OriginalSaving19VertexValuesArrayBlock00300

/-! Original vertex_values array block 4/6; small chunks with arbitrary tails and accumulators.
Exact original bytes are candidate data; the original reader equations below
are the Lean checks. No whole-file decide or replacement reader is used. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def vertexValuesChunk016Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'R', '6', '"', ':', ' ', '"', '2', '3', '8', '4', '1', '5', '7', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'L', '3', '"', ':', ' ', '"', '2', '3', '8', '4', '1', '5', '7', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'B', '3', '"', ':', ' ', '"', '2', '3', '8', '4', '1', '5', '7', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'M', '8', '"', ':', ' ', '"', '2', '3', '8', '4', '1', '5', '7', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '"', ':', ' ', '"', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '1', '0', '6', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '1', '0', '6', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '3', '2', '3', '/', '2', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '2', '7', '8', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '5', '5', '3', '3', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '0', '9', '2', '7', '/', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '0', '9', '2', '7', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '0', '9', '2', '7', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '0', '9', '2', '7', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '3', '6', '8', '7', '/', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def vertexValuesChunk016Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['R', '6'], .str (String.ofList ['2', '3', '8', '4', '1', '5', '7', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['L', '3'], .str (String.ofList ['2', '3', '8', '4', '1', '5', '7', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['B', '3'], .str (String.ofList ['2', '3', '8', '4', '1', '5', '7', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['M', '8'], .str (String.ofList ['2', '3', '8', '4', '1', '5', '7', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['g', 'a', 'p'], .str (String.ofList ['0'])), (String.ofList ['f', 'a', 'c', 't', 'o', 'r', 's'], .arr [.str (String.ofList ['3', '4', '1', '0', '6', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '4', '1', '0', '6', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '3', '2', '3', '/', '2', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '2', '7', '8', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '5', '5', '3', '3', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '0', '9', '2', '7', '/', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '0', '9', '2', '7', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '0', '9', '2', '7', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '0', '9', '2', '7', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '3', '6', '8', '7', '/', '4', '0', '0', '0', '0', '0', '0'])])]) :: (acc)
noncomputable def vertexValuesArrayAcc01700 : List SourceJson := vertexValuesChunk016Push00 vertexValuesArrayAcc01600

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_chunk_016_before"
  err.flush

theorem geometryChars00_vertexValues_chunk_016_prefix :
    (geometryChars00.drop 54788).take 458 = vertexValuesChunk016Chars00 := by rfl

theorem geometryChars00_vertexValues_chunk_016_split :
    geometryChars00.drop 54788 = vertexValuesChunk016Chars00 ++ geometryChars00.drop 55246 := by
  calc
    geometryChars00.drop 54788 =
        (geometryChars00.drop 54788).take 458 ++ (geometryChars00.drop 54788).drop 458 :=
      (List.take_append_drop 458 (geometryChars00.drop 54788)).symm
    _ = vertexValuesChunk016Chars00 ++ (geometryChars00.drop 54788).drop 458 :=
      congrArg (fun p => p ++ (geometryChars00.drop 54788).drop 458) geometryChars00_vertexValues_chunk_016_prefix
    _ = vertexValuesChunk016Chars00 ++ geometryChars00.drop 55246 := by rw [List.drop_drop]

theorem array_vertexValues_chunk_016 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 47)
      (SourceJson.white (vertexValuesChunk016Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 46) (SourceJson.white tail)
        (vertexValuesChunk016Push00 acc) := by rfl

theorem array_vertexValues_original_chunk_016 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 47)
      (SourceJson.white (geometryChars00.drop 54788)) acc =
      SourceJson.array (fuel + 46)
        (SourceJson.white (geometryChars00.drop 55246)) (vertexValuesChunk016Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 47) (SourceJson.white s) acc)
      geometryChars00_vertexValues_chunk_016_split).trans
    (array_vertexValues_chunk_016 fuel (geometryChars00.drop 55246) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_chunk_016_complete"
  err.flush

noncomputable def vertexValuesChunk017Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'R', '6', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'L', '3', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'B', '3', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'M', '8', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '"', ':', ' ', '"', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '8', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '8', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '7', '1', '8', '4', '3', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '9', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '7', '1', '8', '7', '1', '/', '8', '4', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '4', '4', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '4', '4', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '4', '4', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '2', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def vertexValuesChunk017Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['R', '6'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['L', '3'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['B', '3'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['M', '8'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['g', 'a', 'p'], .str (String.ofList ['0'])), (String.ofList ['f', 'a', 'c', 't', 'o', 'r', 's'], .arr [.str (String.ofList ['2', '4', '8', '4', '3', '8', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '8', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '7', '1', '8', '4', '3', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '7', '1', '8', '7', '1', '/', '8', '4', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '4', '4', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '4', '4', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '4', '4', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '2', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0'])])]) :: (acc)
noncomputable def vertexValuesArrayAcc01800 : List SourceJson := vertexValuesChunk017Push00 vertexValuesArrayAcc01700

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_chunk_017_before"
  err.flush

theorem geometryChars00_vertexValues_chunk_017_prefix :
    (geometryChars00.drop 55246).take 477 = vertexValuesChunk017Chars00 := by rfl

theorem geometryChars00_vertexValues_chunk_017_split :
    geometryChars00.drop 55246 = vertexValuesChunk017Chars00 ++ geometryChars00.drop 55723 := by
  calc
    geometryChars00.drop 55246 =
        (geometryChars00.drop 55246).take 477 ++ (geometryChars00.drop 55246).drop 477 :=
      (List.take_append_drop 477 (geometryChars00.drop 55246)).symm
    _ = vertexValuesChunk017Chars00 ++ (geometryChars00.drop 55246).drop 477 :=
      congrArg (fun p => p ++ (geometryChars00.drop 55246).drop 477) geometryChars00_vertexValues_chunk_017_prefix
    _ = vertexValuesChunk017Chars00 ++ geometryChars00.drop 55723 := by rw [List.drop_drop]

theorem array_vertexValues_chunk_017 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 46)
      (SourceJson.white (vertexValuesChunk017Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 45) (SourceJson.white tail)
        (vertexValuesChunk017Push00 acc) := by rfl

theorem array_vertexValues_original_chunk_017 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 46)
      (SourceJson.white (geometryChars00.drop 55246)) acc =
      SourceJson.array (fuel + 45)
        (SourceJson.white (geometryChars00.drop 55723)) (vertexValuesChunk017Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 46) (SourceJson.white s) acc)
      geometryChars00_vertexValues_chunk_017_split).trans
    (array_vertexValues_chunk_017 fuel (geometryChars00.drop 55723) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_chunk_017_complete"
  err.flush

noncomputable def vertexValuesChunk018Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'R', '6', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'L', '3', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'B', '3', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'M', '8', '"', ':', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '"', ':', ' ', '"', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '9', '6', '8', '7', '9', '/', '5', '6', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '9', '6', '8', '7', '9', '/', '5', '6', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '8', '1', '2', '3', '/', '1', '4', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '9', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '5', '3', '1', '1', '7', '/', '1', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '4', '5', '1', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '4', '5', '1', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '9', '6', '8', '7', '9', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '9', '6', '8', '7', '9', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def vertexValuesChunk018Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['R', '6'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['L', '3'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['B', '3'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['M', '8'], .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0'])), (String.ofList ['g', 'a', 'p'], .str (String.ofList ['0'])), (String.ofList ['f', 'a', 'c', 't', 'o', 'r', 's'], .arr [.str (String.ofList ['4', '9', '6', '8', '7', '9', '/', '5', '6', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '9', '6', '8', '7', '9', '/', '5', '6', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '8', '1', '2', '3', '/', '1', '4', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '5', '3', '1', '1', '7', '/', '1', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '4', '5', '1', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '4', '5', '1', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '9', '6', '8', '7', '9', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '9', '6', '8', '7', '9', '/', '1', '6', '8', '0', '0', '0', '0', '0'])])]) :: (acc)
noncomputable def vertexValuesArrayAcc01900 : List SourceJson := vertexValuesChunk018Push00 vertexValuesArrayAcc01800

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_chunk_018_before"
  err.flush

theorem geometryChars00_vertexValues_chunk_018_prefix :
    (geometryChars00.drop 55723).take 471 = vertexValuesChunk018Chars00 := by rfl

theorem geometryChars00_vertexValues_chunk_018_split :
    geometryChars00.drop 55723 = vertexValuesChunk018Chars00 ++ geometryChars00.drop 56194 := by
  calc
    geometryChars00.drop 55723 =
        (geometryChars00.drop 55723).take 471 ++ (geometryChars00.drop 55723).drop 471 :=
      (List.take_append_drop 471 (geometryChars00.drop 55723)).symm
    _ = vertexValuesChunk018Chars00 ++ (geometryChars00.drop 55723).drop 471 :=
      congrArg (fun p => p ++ (geometryChars00.drop 55723).drop 471) geometryChars00_vertexValues_chunk_018_prefix
    _ = vertexValuesChunk018Chars00 ++ geometryChars00.drop 56194 := by rw [List.drop_drop]

theorem array_vertexValues_chunk_018 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 45)
      (SourceJson.white (vertexValuesChunk018Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 44) (SourceJson.white tail)
        (vertexValuesChunk018Push00 acc) := by rfl

theorem array_vertexValues_original_chunk_018 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 45)
      (SourceJson.white (geometryChars00.drop 55723)) acc =
      SourceJson.array (fuel + 44)
        (SourceJson.white (geometryChars00.drop 56194)) (vertexValuesChunk018Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 45) (SourceJson.white s) acc)
      geometryChars00_vertexValues_chunk_018_split).trans
    (array_vertexValues_chunk_018 fuel (geometryChars00.drop 56194) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_chunk_018_complete"
  err.flush

noncomputable def vertexValuesChunk019Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'R', '6', '"', ':', ' ', '"', '1', '6', '6', '9', '6', '8', '5', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'L', '3', '"', ':', ' ', '"', '1', '6', '6', '9', '6', '8', '5', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'B', '3', '"', ':', ' ', '"', '1', '6', '6', '9', '6', '8', '5', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'M', '8', '"', ':', ' ', '"', '1', '6', '6', '9', '6', '8', '5', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '"', ':', ' ', '"', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '8', '9', '3', '8', '1', '/', '5', '6', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '8', '9', '3', '8', '1', '/', '5', '6', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '8', '1', '2', '3', '/', '1', '4', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '4', '6', '8', '8', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '8', '1', '1', '9', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '1', '5', '6', '2', '7', '/', '1', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '1', '5', '6', '2', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '1', '5', '6', '2', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '3', '1', '2', '7', '/', '5', '6', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '3', '1', '2', '7', '/', '5', '6', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def vertexValuesChunk019Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['R', '6'], .str (String.ofList ['1', '6', '6', '9', '6', '8', '5', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0'])), (String.ofList ['L', '3'], .str (String.ofList ['1', '6', '6', '9', '6', '8', '5', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0'])), (String.ofList ['B', '3'], .str (String.ofList ['1', '6', '6', '9', '6', '8', '5', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0'])), (String.ofList ['M', '8'], .str (String.ofList ['1', '6', '6', '9', '6', '8', '5', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0'])), (String.ofList ['g', 'a', 'p'], .str (String.ofList ['0'])), (String.ofList ['f', 'a', 'c', 't', 'o', 'r', 's'], .arr [.str (String.ofList ['4', '8', '9', '3', '8', '1', '/', '5', '6', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '8', '9', '3', '8', '1', '/', '5', '6', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '8', '1', '2', '3', '/', '1', '4', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '4', '6', '8', '8', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '8', '1', '1', '9', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '1', '5', '6', '2', '7', '/', '1', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '1', '5', '6', '2', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '1', '5', '6', '2', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '3', '1', '2', '7', '/', '5', '6', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '3', '1', '2', '7', '/', '5', '6', '0', '0', '0', '0', '0'])])]) :: (acc)
noncomputable def vertexValuesArrayAcc02000 : List SourceJson := vertexValuesChunk019Push00 vertexValuesArrayAcc01900

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_chunk_019_before"
  err.flush

theorem geometryChars00_vertexValues_chunk_019_prefix :
    (geometryChars00.drop 56194).take 473 = vertexValuesChunk019Chars00 := by rfl

theorem geometryChars00_vertexValues_chunk_019_split :
    geometryChars00.drop 56194 = vertexValuesChunk019Chars00 ++ geometryChars00.drop 56667 := by
  calc
    geometryChars00.drop 56194 =
        (geometryChars00.drop 56194).take 473 ++ (geometryChars00.drop 56194).drop 473 :=
      (List.take_append_drop 473 (geometryChars00.drop 56194)).symm
    _ = vertexValuesChunk019Chars00 ++ (geometryChars00.drop 56194).drop 473 :=
      congrArg (fun p => p ++ (geometryChars00.drop 56194).drop 473) geometryChars00_vertexValues_chunk_019_prefix
    _ = vertexValuesChunk019Chars00 ++ geometryChars00.drop 56667 := by rw [List.drop_drop]

theorem array_vertexValues_chunk_019 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 44)
      (SourceJson.white (vertexValuesChunk019Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 43) (SourceJson.white tail)
        (vertexValuesChunk019Push00 acc) := by rfl

theorem array_vertexValues_original_chunk_019 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 44)
      (SourceJson.white (geometryChars00.drop 56194)) acc =
      SourceJson.array (fuel + 43)
        (SourceJson.white (geometryChars00.drop 56667)) (vertexValuesChunk019Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 44) (SourceJson.white s) acc)
      geometryChars00_vertexValues_chunk_019_split).trans
    (array_vertexValues_chunk_019 fuel (geometryChars00.drop 56667) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_chunk_019_complete"
  err.flush

theorem vertexValues_array_through_block_004 (fuel : Nat) :
    SourceJson.array (fuel + 63)
      (SourceJson.white (geometryChars00.drop 46997)) [] =
      SourceJson.array (fuel + 43)
        (SourceJson.white (geometryChars00.drop 56667)) vertexValuesArrayAcc02000 := by
  calc
    SourceJson.array (fuel + 63)
        (SourceJson.white (geometryChars00.drop 46997)) [] =
      SourceJson.array (fuel + 47)
        (SourceJson.white (geometryChars00.drop 54788)) vertexValuesArrayAcc01600 :=
      vertexValues_array_through_block_003 fuel
    _ =
      SourceJson.array (fuel + 46)
        (SourceJson.white (geometryChars00.drop 55246)) vertexValuesArrayAcc01700 :=
      array_vertexValues_original_chunk_016 fuel vertexValuesArrayAcc01600
    _ =
      SourceJson.array (fuel + 45)
        (SourceJson.white (geometryChars00.drop 55723)) vertexValuesArrayAcc01800 :=
      array_vertexValues_original_chunk_017 fuel vertexValuesArrayAcc01700
    _ =
      SourceJson.array (fuel + 44)
        (SourceJson.white (geometryChars00.drop 56194)) vertexValuesArrayAcc01900 :=
      array_vertexValues_original_chunk_018 fuel vertexValuesArrayAcc01800
    _ =
      SourceJson.array (fuel + 43)
        (SourceJson.white (geometryChars00.drop 56667)) vertexValuesArrayAcc02000 :=
      array_vertexValues_original_chunk_019 fuel vertexValuesArrayAcc01900

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 vertexValues_block_004_complete"
  err.flush

#print axioms geometryChars00_vertexValues_chunk_016_prefix
#print axioms geometryChars00_vertexValues_chunk_016_split
#print axioms array_vertexValues_chunk_016
#print axioms array_vertexValues_original_chunk_016
#print axioms geometryChars00_vertexValues_chunk_017_prefix
#print axioms geometryChars00_vertexValues_chunk_017_split
#print axioms array_vertexValues_chunk_017
#print axioms array_vertexValues_original_chunk_017
#print axioms geometryChars00_vertexValues_chunk_018_prefix
#print axioms geometryChars00_vertexValues_chunk_018_split
#print axioms array_vertexValues_chunk_018
#print axioms array_vertexValues_original_chunk_018
#print axioms geometryChars00_vertexValues_chunk_019_prefix
#print axioms geometryChars00_vertexValues_chunk_019_split
#print axioms array_vertexValues_chunk_019
#print axioms array_vertexValues_original_chunk_019
#print axioms vertexValues_array_through_block_004

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
