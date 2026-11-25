import ImbalancedChen.P2OriginalSaving19VertexValuesField00

/-! Original all_original_constraint_minima array block 0/1; small chunks with arbitrary tails and accumulators.
Exact original bytes are candidate data; the original reader equations below
are the Lean checks. No whole-file decide or replacement reader is used. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def constraintMinimaOpenChars00 : List Char := ['[']
noncomputable def constraintMinimaArrayAcc00000 : List SourceJson := []

theorem geometryChars00_constraintMinima_open_prefix :
    (geometryChars00.drop 60487).take 1 = constraintMinimaOpenChars00 := by rfl

theorem geometryChars00_constraintMinima_open_split :
    geometryChars00.drop 60487 = constraintMinimaOpenChars00 ++ geometryChars00.drop 60488 := by
  calc
    geometryChars00.drop 60487 =
        (geometryChars00.drop 60487).take 1 ++ (geometryChars00.drop 60487).drop 1 :=
      (List.take_append_drop 1 (geometryChars00.drop 60487)).symm
    _ = constraintMinimaOpenChars00 ++ (geometryChars00.drop 60487).drop 1 :=
      congrArg (fun p => p ++ (geometryChars00.drop 60487).drop 1) geometryChars00_constraintMinima_open_prefix
    _ = constraintMinimaOpenChars00 ++ geometryChars00.drop 60488 := by rw [List.drop_drop]

theorem value_constraintMinima_open (fuel : Nat) :
    SourceJson.value (fuel + 117) (geometryChars00.drop 60487) =
      SourceJson.array (fuel + 116)
        (SourceJson.white (geometryChars00.drop 60488)) [] := by
  calc
    SourceJson.value (fuel + 117) (geometryChars00.drop 60487) =
        SourceJson.value (fuel + 117)
          (constraintMinimaOpenChars00 ++ geometryChars00.drop 60488) :=
      congrArg (SourceJson.value (fuel + 117)) geometryChars00_constraintMinima_open_split
    _ = SourceJson.array (fuel + 116)
        (SourceJson.white (geometryChars00.drop 60488)) [] := by rfl

noncomputable def constraintMinimaChunk000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '5', '2', '7', '/', '4', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '8', '4', '9', '7', '9', '/', '1', '4', '4', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '6', '5', '9', '1', '2', '7', '3', '/', '7', '3', '4', '4', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '4', '9', '8', '4', '2', '8', '3', '/', '2', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '/', '3', '7', '5', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '/', '3', '7', '5', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '5', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '5', '2', '9', '7', '1', '5', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '2', '7', '6', '5', '9', '0', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '1', '6', '8', '2', '0', '1', '/', '1', '2', '4', '8', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '9', '6', '1', '1', '3', '6', '3', '/', '3', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '/', '2', '5', '0', '0', '0', '0', '"', ',']
noncomputable def constraintMinimaChunk000Push00 (acc : List SourceJson) : List SourceJson :=
  (.str (String.ofList ['1', '/', '2', '5', '0', '0', '0', '0'])) :: ((.str (String.ofList ['0'])) :: ((.str (String.ofList ['9', '6', '1', '1', '3', '6', '3', '/', '3', '6', '0', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['1', '1', '6', '8', '2', '0', '1', '/', '1', '2', '4', '8', '0', '0', '0', '0'])) :: ((.str (String.ofList ['2', '7', '6', '5', '9', '0', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['5', '2', '9', '7', '1', '5', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['0'])) :: ((.str (String.ofList ['0'])) :: ((.str (String.ofList ['0'])) :: ((.str (String.ofList ['5', '1', '0', '9', '5', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['1', '/', '3', '7', '5', '0', '0', '0'])) :: ((.str (String.ofList ['1', '/', '3', '7', '5', '0', '0', '0'])) :: ((.str (String.ofList ['4', '9', '8', '4', '2', '8', '3', '/', '2', '1', '2', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['1', '6', '5', '9', '1', '2', '7', '3', '/', '7', '3', '4', '4', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['8', '4', '9', '7', '9', '/', '1', '4', '4', '0', '0', '0', '0'])) :: ((.str (String.ofList ['2', '4', '8', '4', '5', '2', '7', '/', '4', '2', '0', '0', '0', '0', '0', '0'])) :: (acc))))))))))))))))
noncomputable def constraintMinimaArrayAcc00100 : List SourceJson := constraintMinimaChunk000Push00 constraintMinimaArrayAcc00000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 constraintMinima_chunk_000_before"
  err.flush

theorem geometryChars00_constraintMinima_chunk_000_prefix :
    (geometryChars00.drop 60488).take 318 = constraintMinimaChunk000Chars00 := by rfl

theorem geometryChars00_constraintMinima_chunk_000_split :
    geometryChars00.drop 60488 = constraintMinimaChunk000Chars00 ++ geometryChars00.drop 60806 := by
  calc
    geometryChars00.drop 60488 =
        (geometryChars00.drop 60488).take 318 ++ (geometryChars00.drop 60488).drop 318 :=
      (List.take_append_drop 318 (geometryChars00.drop 60488)).symm
    _ = constraintMinimaChunk000Chars00 ++ (geometryChars00.drop 60488).drop 318 :=
      congrArg (fun p => p ++ (geometryChars00.drop 60488).drop 318) geometryChars00_constraintMinima_chunk_000_prefix
    _ = constraintMinimaChunk000Chars00 ++ geometryChars00.drop 60806 := by rw [List.drop_drop]

theorem array_constraintMinima_chunk_000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 116)
      (SourceJson.white (constraintMinimaChunk000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 100) (SourceJson.white tail)
        (constraintMinimaChunk000Push00 acc) := by rfl

theorem array_constraintMinima_original_chunk_000 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 116)
      (SourceJson.white (geometryChars00.drop 60488)) acc =
      SourceJson.array (fuel + 100)
        (SourceJson.white (geometryChars00.drop 60806)) (constraintMinimaChunk000Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 116) (SourceJson.white s) acc)
      geometryChars00_constraintMinima_chunk_000_split).trans
    (array_constraintMinima_chunk_000 fuel (geometryChars00.drop 60806) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 constraintMinima_chunk_000_complete"
  err.flush

noncomputable def constraintMinimaChunk001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '7', '9', '/', '9', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '/', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '2', '7', '3', '2', '8', '6', '4', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '0', '9', '2', '2', '3', '9', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '6', '9', '5', '3', '2', '9', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '2', '5', '6', '2', '9', '/', '7', '2', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '2', '7', '6', '5', '8', '3', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '1', '6', '7', '2', '1', '6', '7', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '8', '0', '1', '5', '9', '0', '9', '/', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '4', '7', '3', '4', '5', '6', '9', '/', '4', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '3', '5', '9', '3', '8', '7', '/', '3', '4', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '2', '7', '6', '5', '7', '4', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '4', '8', '9', '0', '8', '7', '7', '/', '6', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '7', '9', '6', '9', '3', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '"', ',']
noncomputable def constraintMinimaChunk001Push00 (acc : List SourceJson) : List SourceJson :=
  (.str (String.ofList ['7', '9', '6', '9', '3', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['4', '8', '9', '0', '8', '7', '7', '/', '6', '8', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['2', '7', '6', '5', '7', '4', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['3', '5', '9', '3', '8', '7', '/', '3', '4', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['4', '7', '3', '4', '5', '6', '9', '/', '4', '5', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['8', '0', '1', '5', '9', '0', '9', '/', '6', '0', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['1', '1', '6', '7', '2', '1', '6', '7', '/', '8', '4', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['2', '7', '6', '5', '8', '3', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['1', '2', '5', '6', '2', '9', '/', '7', '2', '0', '0', '0', '0'])) :: ((.str (String.ofList ['6', '9', '5', '3', '2', '9', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['1', '0', '9', '2', '2', '3', '9', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['2', '7', '3', '2', '8', '6', '4', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['0'])) :: ((.str (String.ofList ['0'])) :: ((.str (String.ofList ['1', '/', '5', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['2', '4', '8', '4', '3', '7', '9', '/', '9', '6', '0', '0', '0', '0', '0', '0'])) :: (acc))))))))))))))))
noncomputable def constraintMinimaArrayAcc00200 : List SourceJson := constraintMinimaChunk001Push00 constraintMinimaArrayAcc00100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 constraintMinima_chunk_001_before"
  err.flush

theorem geometryChars00_constraintMinima_chunk_001_prefix :
    (geometryChars00.drop 60806).take 359 = constraintMinimaChunk001Chars00 := by rfl

theorem geometryChars00_constraintMinima_chunk_001_split :
    geometryChars00.drop 60806 = constraintMinimaChunk001Chars00 ++ geometryChars00.drop 61165 := by
  calc
    geometryChars00.drop 60806 =
        (geometryChars00.drop 60806).take 359 ++ (geometryChars00.drop 60806).drop 359 :=
      (List.take_append_drop 359 (geometryChars00.drop 60806)).symm
    _ = constraintMinimaChunk001Chars00 ++ (geometryChars00.drop 60806).drop 359 :=
      congrArg (fun p => p ++ (geometryChars00.drop 60806).drop 359) geometryChars00_constraintMinima_chunk_001_prefix
    _ = constraintMinimaChunk001Chars00 ++ geometryChars00.drop 61165 := by rw [List.drop_drop]

theorem array_constraintMinima_chunk_001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 100)
      (SourceJson.white (constraintMinimaChunk001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 84) (SourceJson.white tail)
        (constraintMinimaChunk001Push00 acc) := by rfl

theorem array_constraintMinima_original_chunk_001 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 100)
      (SourceJson.white (geometryChars00.drop 60806)) acc =
      SourceJson.array (fuel + 84)
        (SourceJson.white (geometryChars00.drop 61165)) (constraintMinimaChunk001Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 100) (SourceJson.white s) acc)
      geometryChars00_constraintMinima_chunk_001_split).trans
    (array_constraintMinima_chunk_001 fuel (geometryChars00.drop 61165) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 constraintMinima_chunk_001_complete"
  err.flush

noncomputable def constraintMinimaChunk002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '7', '9', '6', '9', '4', '3', '/', '1', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '7', '9', '6', '9', '4', '3', '/', '1', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '4', '4', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '4', '9', '0', '6', '2', '1', '/', '3', '3', '6', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '/', '2', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '9', '2', '7', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '6', '5', '4', '6', '9', '2', '7', '/', '2', '8', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '4', '9', '8', '4', '2', '8', '3', '/', '4', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '8', '7', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '4', '4', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '7', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '5', '7', '1', '/', '4', '8', '0', '0', '0', '0', '0', '0', '"', ',']
noncomputable def constraintMinimaChunk002Push00 (acc : List SourceJson) : List SourceJson :=
  (.str (String.ofList ['2', '4', '8', '4', '5', '7', '1', '/', '4', '8', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['2', '4', '8', '4', '3', '7', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['2', '4', '8', '4', '4', '4', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['1', '1', '7', '1', '8', '8', '7', '/', '1', '0', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['4', '9', '8', '4', '2', '8', '3', '/', '4', '2', '4', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['1', '6', '5', '4', '6', '9', '2', '7', '/', '2', '8', '8', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['1', '1', '7', '1', '9', '2', '7', '/', '1', '0', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['0'])) :: ((.str (String.ofList ['0'])) :: ((.str (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['1', '/', '2', '5', '0', '0', '0', '0'])) :: ((.str (String.ofList ['1', '4', '9', '0', '6', '2', '1', '/', '3', '3', '6', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['2', '4', '8', '4', '4', '4', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['0'])) :: ((.str (String.ofList ['7', '9', '6', '9', '4', '3', '/', '1', '8', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['7', '9', '6', '9', '4', '3', '/', '1', '8', '0', '0', '0', '0', '0', '0'])) :: (acc))))))))))))))))
noncomputable def constraintMinimaArrayAcc00300 : List SourceJson := constraintMinimaChunk002Push00 constraintMinimaArrayAcc00200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 constraintMinima_chunk_002_before"
  err.flush

theorem geometryChars00_constraintMinima_chunk_002_prefix :
    (geometryChars00.drop 61165).take 349 = constraintMinimaChunk002Chars00 := by rfl

theorem geometryChars00_constraintMinima_chunk_002_split :
    geometryChars00.drop 61165 = constraintMinimaChunk002Chars00 ++ geometryChars00.drop 61514 := by
  calc
    geometryChars00.drop 61165 =
        (geometryChars00.drop 61165).take 349 ++ (geometryChars00.drop 61165).drop 349 :=
      (List.take_append_drop 349 (geometryChars00.drop 61165)).symm
    _ = constraintMinimaChunk002Chars00 ++ (geometryChars00.drop 61165).drop 349 :=
      congrArg (fun p => p ++ (geometryChars00.drop 61165).drop 349) geometryChars00_constraintMinima_chunk_002_prefix
    _ = constraintMinimaChunk002Chars00 ++ geometryChars00.drop 61514 := by rw [List.drop_drop]

theorem array_constraintMinima_chunk_002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 84)
      (SourceJson.white (constraintMinimaChunk002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 68) (SourceJson.white tail)
        (constraintMinimaChunk002Push00 acc) := by rfl

theorem array_constraintMinima_original_chunk_002 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 84)
      (SourceJson.white (geometryChars00.drop 61165)) acc =
      SourceJson.array (fuel + 68)
        (SourceJson.white (geometryChars00.drop 61514)) (constraintMinimaChunk002Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 84) (SourceJson.white s) acc)
      geometryChars00_constraintMinima_chunk_002_split).trans
    (array_constraintMinima_chunk_002 fuel (geometryChars00.drop 61514) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 constraintMinima_chunk_002_complete"
  err.flush

noncomputable def constraintMinimaChunk003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '8', '7', '/', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '3', '9', '5', '3', '1', '2', '1', '/', '5', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '5', '7', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '5', '9', '8', '4', '3', '3', '1', '/', '2', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '5', '7', '1', '/', '4', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '7', '9', '/', '4', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '/', '2', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '6', '5', '4', '7', '3', '1', '1', '/', '9', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '1', '8', '5', '9', '5', '7', '1', '/', '3', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '4', '9', '5', '2', '8', '4', '9', '/', '4', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '6', '5', '4', '6', '9', '2', '7', '/', '9', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '7', '9', '/', '1', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '9', '9', '3', '7', '9', '/', '9', '6', '0', '0', '0', '0', '"', ',']
noncomputable def constraintMinimaChunk003Push00 (acc : List SourceJson) : List SourceJson :=
  (.str (String.ofList ['9', '9', '3', '7', '9', '/', '9', '6', '0', '0', '0', '0'])) :: ((.str (String.ofList ['2', '4', '8', '4', '3', '7', '9', '/', '1', '6', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['0'])) :: ((.str (String.ofList ['1', '6', '5', '4', '6', '9', '2', '7', '/', '9', '6', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['0'])) :: ((.str (String.ofList ['1', '4', '9', '5', '2', '8', '4', '9', '/', '4', '2', '4', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['1', '1', '8', '5', '9', '5', '7', '1', '/', '3', '1', '2', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['1', '6', '5', '4', '7', '3', '1', '1', '/', '9', '6', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['1', '/', '2', '5', '0', '0', '0', '0'])) :: ((.str (String.ofList ['2', '4', '8', '4', '3', '7', '9', '/', '4', '8', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['2', '4', '8', '4', '5', '7', '1', '/', '4', '8', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['5', '9', '8', '4', '3', '3', '1', '/', '2', '1', '2', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['5', '1', '0', '9', '5', '7', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['3', '9', '5', '3', '1', '2', '1', '/', '5', '2', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['1', '1', '7', '1', '8', '8', '7', '/', '5', '0', '0', '0', '0', '0', '0'])) :: (acc))))))))))))))))
noncomputable def constraintMinimaArrayAcc00400 : List SourceJson := constraintMinimaChunk003Push00 constraintMinimaArrayAcc00300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 constraintMinima_chunk_003_before"
  err.flush

theorem geometryChars00_constraintMinima_chunk_003_prefix :
    (geometryChars00.drop 61514).take 365 = constraintMinimaChunk003Chars00 := by rfl

theorem geometryChars00_constraintMinima_chunk_003_split :
    geometryChars00.drop 61514 = constraintMinimaChunk003Chars00 ++ geometryChars00.drop 61879 := by
  calc
    geometryChars00.drop 61514 =
        (geometryChars00.drop 61514).take 365 ++ (geometryChars00.drop 61514).drop 365 :=
      (List.take_append_drop 365 (geometryChars00.drop 61514)).symm
    _ = constraintMinimaChunk003Chars00 ++ (geometryChars00.drop 61514).drop 365 :=
      congrArg (fun p => p ++ (geometryChars00.drop 61514).drop 365) geometryChars00_constraintMinima_chunk_003_prefix
    _ = constraintMinimaChunk003Chars00 ++ geometryChars00.drop 61879 := by rw [List.drop_drop]

theorem array_constraintMinima_chunk_003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 68)
      (SourceJson.white (constraintMinimaChunk003Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 52) (SourceJson.white tail)
        (constraintMinimaChunk003Push00 acc) := by rfl

theorem array_constraintMinima_original_chunk_003 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 68)
      (SourceJson.white (geometryChars00.drop 61514)) acc =
      SourceJson.array (fuel + 52)
        (SourceJson.white (geometryChars00.drop 61879)) (constraintMinimaChunk003Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 68) (SourceJson.white s) acc)
      geometryChars00_constraintMinima_chunk_003_split).trans
    (array_constraintMinima_chunk_003 fuel (geometryChars00.drop 61879) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 constraintMinima_chunk_003_complete"
  err.flush

theorem constraintMinima_array_through_block_000 (fuel : Nat) :
    SourceJson.array (fuel + 116)
      (SourceJson.white (geometryChars00.drop 60488)) [] =
      SourceJson.array (fuel + 52)
        (SourceJson.white (geometryChars00.drop 61879)) constraintMinimaArrayAcc00400 := by
  calc
    SourceJson.array (fuel + 116)
        (SourceJson.white (geometryChars00.drop 60488)) [] =
      SourceJson.array (fuel + 100)
        (SourceJson.white (geometryChars00.drop 60806)) constraintMinimaArrayAcc00100 :=
      array_constraintMinima_original_chunk_000 fuel constraintMinimaArrayAcc00000
    _ =
      SourceJson.array (fuel + 84)
        (SourceJson.white (geometryChars00.drop 61165)) constraintMinimaArrayAcc00200 :=
      array_constraintMinima_original_chunk_001 fuel constraintMinimaArrayAcc00100
    _ =
      SourceJson.array (fuel + 68)
        (SourceJson.white (geometryChars00.drop 61514)) constraintMinimaArrayAcc00300 :=
      array_constraintMinima_original_chunk_002 fuel constraintMinimaArrayAcc00200
    _ =
      SourceJson.array (fuel + 52)
        (SourceJson.white (geometryChars00.drop 61879)) constraintMinimaArrayAcc00400 :=
      array_constraintMinima_original_chunk_003 fuel constraintMinimaArrayAcc00300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 constraintMinima_block_000_complete"
  err.flush

#print axioms geometryChars00_constraintMinima_open_prefix
#print axioms geometryChars00_constraintMinima_open_split
#print axioms value_constraintMinima_open
#print axioms geometryChars00_constraintMinima_chunk_000_prefix
#print axioms geometryChars00_constraintMinima_chunk_000_split
#print axioms array_constraintMinima_chunk_000
#print axioms array_constraintMinima_original_chunk_000
#print axioms geometryChars00_constraintMinima_chunk_001_prefix
#print axioms geometryChars00_constraintMinima_chunk_001_split
#print axioms array_constraintMinima_chunk_001
#print axioms array_constraintMinima_original_chunk_001
#print axioms geometryChars00_constraintMinima_chunk_002_prefix
#print axioms geometryChars00_constraintMinima_chunk_002_split
#print axioms array_constraintMinima_chunk_002
#print axioms array_constraintMinima_original_chunk_002
#print axioms geometryChars00_constraintMinima_chunk_003_prefix
#print axioms geometryChars00_constraintMinima_chunk_003_split
#print axioms array_constraintMinima_chunk_003
#print axioms array_constraintMinima_original_chunk_003
#print axioms constraintMinima_array_through_block_000

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
