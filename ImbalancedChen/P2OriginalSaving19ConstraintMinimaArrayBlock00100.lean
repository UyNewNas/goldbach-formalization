import ImbalancedChen.P2OriginalSaving19ConstraintMinimaArrayBlock00000

/-! Original all_original_constraint_minima array block 1/1; small chunks with arbitrary tails and accumulators.
Exact original bytes are candidate data; the original reader equations below
are the Lean checks. No whole-file decide or replacement reader is used. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def constraintMinimaChunk004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '9', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '3', '9', '5', '3', '1', '2', '1', '/', '5', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '4', '4', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '5', '9', '8', '4', '3', '3', '1', '/', '2', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '5', '7', '1', '/', '4', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '4', '4', '3', '/', '1', '0', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '/', '2', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '6', '5', '4', '7', '3', '1', '1', '/', '9', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '4', '9', '5', '2', '8', '4', '9', '/', '4', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '6', '5', '4', '6', '9', '2', '7', '/', '9', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '7', '9', '/', '1', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '9', '9', '3', '7', '9', '/', '9', '6', '0', '0', '0', '0', '"', ',']
noncomputable def constraintMinimaChunk004Push00 (acc : List SourceJson) : List SourceJson :=
  (.str (String.ofList ['9', '9', '3', '7', '9', '/', '9', '6', '0', '0', '0', '0'])) :: ((.str (String.ofList ['2', '4', '8', '4', '3', '7', '9', '/', '1', '6', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['0'])) :: ((.str (String.ofList ['1', '6', '5', '4', '6', '9', '2', '7', '/', '9', '6', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['0'])) :: ((.str (String.ofList ['1', '4', '9', '5', '2', '8', '4', '9', '/', '4', '2', '4', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['3', '9', '0', '6', '2', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['1', '6', '5', '4', '7', '3', '1', '1', '/', '9', '6', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['1', '/', '2', '5', '0', '0', '0', '0'])) :: ((.str (String.ofList ['5', '1', '0', '9', '4', '4', '3', '/', '1', '0', '4', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['2', '4', '8', '4', '5', '7', '1', '/', '4', '8', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['5', '9', '8', '4', '3', '3', '1', '/', '2', '1', '2', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['2', '4', '8', '4', '4', '4', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['3', '9', '5', '3', '1', '2', '1', '/', '5', '2', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '4', '0', '0', '0', '0', '0', '0'])) :: (acc))))))))))))))))
noncomputable def constraintMinimaArrayAcc00500 : List SourceJson := constraintMinimaChunk004Push00 constraintMinimaArrayAcc00400

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 constraintMinima_chunk_004_before"
  err.flush

theorem geometryChars00_constraintMinima_chunk_004_prefix :
    (geometryChars00.drop 61879).take 363 = constraintMinimaChunk004Chars00 := by rfl

theorem geometryChars00_constraintMinima_chunk_004_split :
    geometryChars00.drop 61879 = constraintMinimaChunk004Chars00 ++ geometryChars00.drop 62242 := by
  calc
    geometryChars00.drop 61879 =
        (geometryChars00.drop 61879).take 363 ++ (geometryChars00.drop 61879).drop 363 :=
      (List.take_append_drop 363 (geometryChars00.drop 61879)).symm
    _ = constraintMinimaChunk004Chars00 ++ (geometryChars00.drop 61879).drop 363 :=
      congrArg (fun p => p ++ (geometryChars00.drop 61879).drop 363) geometryChars00_constraintMinima_chunk_004_prefix
    _ = constraintMinimaChunk004Chars00 ++ geometryChars00.drop 62242 := by rw [List.drop_drop]

theorem array_constraintMinima_chunk_004 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 52)
      (SourceJson.white (constraintMinimaChunk004Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 36) (SourceJson.white tail)
        (constraintMinimaChunk004Push00 acc) := by rfl

theorem array_constraintMinima_original_chunk_004 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 52)
      (SourceJson.white (geometryChars00.drop 61879)) acc =
      SourceJson.array (fuel + 36)
        (SourceJson.white (geometryChars00.drop 62242)) (constraintMinimaChunk004Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 52) (SourceJson.white s) acc)
      geometryChars00_constraintMinima_chunk_004_split).trans
    (array_constraintMinima_chunk_004 fuel (geometryChars00.drop 62242) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 constraintMinima_chunk_004_complete"
  err.flush

noncomputable def constraintMinimaChunk005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '9', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '2', '4', '2', '6', '5', '6', '2', '1', '/', '4', '1', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '4', '9', '8', '4', '2', '8', '3', '/', '4', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '9', '9', '3', '7', '9', '/', '9', '6', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '9', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '7', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '5', '7', '1', '/', '4', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '7', '1', '7', '2', '0', '2', '3', '/', '3', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '9', '2', '7', '/', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '7', '9', '5', '2', '9', '9', '3', '/', '2', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '4', '4', '3', '/', '5', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '4', '3', '4', '3', '7', '9', '/', '6', '4', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '4', '0', '6', '5', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '7', '9', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '4', '4', '3', '/', '1', '6', '0', '0', '0', '0', '0', '0', '"', ',']
noncomputable def constraintMinimaChunk005Push00 (acc : List SourceJson) : List SourceJson :=
  (.str (String.ofList ['2', '4', '8', '4', '4', '4', '3', '/', '1', '6', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['2', '4', '8', '4', '3', '7', '9', '/', '1', '2', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['1', '4', '0', '6', '5', '3', '/', '8', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['1', '4', '3', '4', '3', '7', '9', '/', '6', '4', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['2', '4', '8', '4', '4', '4', '3', '/', '5', '6', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['1', '7', '9', '5', '2', '9', '9', '3', '/', '2', '1', '2', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['1', '1', '7', '1', '9', '2', '7', '/', '6', '0', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['7', '1', '7', '2', '0', '2', '3', '/', '3', '2', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['2', '4', '8', '4', '5', '7', '1', '/', '4', '8', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['2', '4', '8', '4', '3', '7', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '7', '2', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['9', '9', '3', '7', '9', '/', '9', '6', '0', '0', '0', '0'])) :: ((.str (String.ofList ['4', '9', '8', '4', '2', '8', '3', '/', '4', '2', '4', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['0'])) :: ((.str (String.ofList ['2', '4', '2', '6', '5', '6', '2', '1', '/', '4', '1', '6', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '4', '0', '0', '0', '0', '0', '0'])) :: (acc))))))))))))))))
noncomputable def constraintMinimaArrayAcc00600 : List SourceJson := constraintMinimaChunk005Push00 constraintMinimaArrayAcc00500

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 constraintMinima_chunk_005_before"
  err.flush

theorem geometryChars00_constraintMinima_chunk_005_prefix :
    (geometryChars00.drop 62242).take 382 = constraintMinimaChunk005Chars00 := by rfl

theorem geometryChars00_constraintMinima_chunk_005_split :
    geometryChars00.drop 62242 = constraintMinimaChunk005Chars00 ++ geometryChars00.drop 62624 := by
  calc
    geometryChars00.drop 62242 =
        (geometryChars00.drop 62242).take 382 ++ (geometryChars00.drop 62242).drop 382 :=
      (List.take_append_drop 382 (geometryChars00.drop 62242)).symm
    _ = constraintMinimaChunk005Chars00 ++ (geometryChars00.drop 62242).drop 382 :=
      congrArg (fun p => p ++ (geometryChars00.drop 62242).drop 382) geometryChars00_constraintMinima_chunk_005_prefix
    _ = constraintMinimaChunk005Chars00 ++ geometryChars00.drop 62624 := by rw [List.drop_drop]

theorem array_constraintMinima_chunk_005 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 36)
      (SourceJson.white (constraintMinimaChunk005Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 20) (SourceJson.white tail)
        (constraintMinimaChunk005Push00 acc) := by rfl

theorem array_constraintMinima_original_chunk_005 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 36)
      (SourceJson.white (geometryChars00.drop 62242)) acc =
      SourceJson.array (fuel + 20)
        (SourceJson.white (geometryChars00.drop 62624)) (constraintMinimaChunk005Push00 acc) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 36) (SourceJson.white s) acc)
      geometryChars00_constraintMinima_chunk_005_split).trans
    (array_constraintMinima_chunk_005 fuel (geometryChars00.drop 62624) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 constraintMinima_chunk_005_complete"
  err.flush

noncomputable def constraintMinimaChunk006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '6', '5', '4', '6', '9', '2', '7', '/', '4', '8', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ']']
noncomputable def constraintMinimaChunk006Push00 (acc : List SourceJson) : List SourceJson :=
  (.str (String.ofList ['1', '6', '5', '4', '6', '9', '2', '7', '/', '4', '8', '0', '0', '0', '0', '0', '0'])) :: (acc)
noncomputable def constraintMinimaArrayAcc00700 : List SourceJson := constraintMinimaChunk006Push00 constraintMinimaArrayAcc00600

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 constraintMinima_chunk_006_before"
  err.flush

theorem geometryChars00_constraintMinima_chunk_006_prefix :
    (geometryChars00.drop 62624).take 30 = constraintMinimaChunk006Chars00 := by rfl

theorem geometryChars00_constraintMinima_chunk_006_split :
    geometryChars00.drop 62624 = constraintMinimaChunk006Chars00 ++ geometryChars00.drop 62654 := by
  calc
    geometryChars00.drop 62624 =
        (geometryChars00.drop 62624).take 30 ++ (geometryChars00.drop 62624).drop 30 :=
      (List.take_append_drop 30 (geometryChars00.drop 62624)).symm
    _ = constraintMinimaChunk006Chars00 ++ (geometryChars00.drop 62624).drop 30 :=
      congrArg (fun p => p ++ (geometryChars00.drop 62624).drop 30) geometryChars00_constraintMinima_chunk_006_prefix
    _ = constraintMinimaChunk006Chars00 ++ geometryChars00.drop 62654 := by rw [List.drop_drop]

theorem array_constraintMinima_chunk_006 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 20)
      (SourceJson.white (constraintMinimaChunk006Chars00 ++ tail)) acc =
      .ok (.arr ((constraintMinimaChunk006Push00 acc).reverse), tail) := by rfl

theorem array_constraintMinima_original_chunk_006 (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 20)
      (SourceJson.white (geometryChars00.drop 62624)) acc =
      .ok (.arr ((constraintMinimaChunk006Push00 acc).reverse), geometryChars00.drop 62654) := by
  exact (congrArg (fun s => SourceJson.array (fuel + 20) (SourceJson.white s) acc)
      geometryChars00_constraintMinima_chunk_006_split).trans
    (array_constraintMinima_chunk_006 fuel (geometryChars00.drop 62654) acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 constraintMinima_chunk_006_complete"
  err.flush

noncomputable def constraintMinimaArrayValue00 : SourceJson := .arr (constraintMinimaArrayAcc00700.reverse)

theorem constraintMinima_array_through_block_001 (fuel : Nat) :
    SourceJson.array (fuel + 116)
      (SourceJson.white (geometryChars00.drop 60488)) [] =
      .ok (constraintMinimaArrayValue00, geometryChars00.drop 62654) := by
  calc
    SourceJson.array (fuel + 116)
        (SourceJson.white (geometryChars00.drop 60488)) [] =
      SourceJson.array (fuel + 52)
        (SourceJson.white (geometryChars00.drop 61879)) constraintMinimaArrayAcc00400 :=
      constraintMinima_array_through_block_000 fuel
    _ =
      SourceJson.array (fuel + 36)
        (SourceJson.white (geometryChars00.drop 62242)) constraintMinimaArrayAcc00500 :=
      array_constraintMinima_original_chunk_004 fuel constraintMinimaArrayAcc00400
    _ =
      SourceJson.array (fuel + 20)
        (SourceJson.white (geometryChars00.drop 62624)) constraintMinimaArrayAcc00600 :=
      array_constraintMinima_original_chunk_005 fuel constraintMinimaArrayAcc00500
    _ =
      .ok (constraintMinimaArrayValue00, geometryChars00.drop 62654) :=
      array_constraintMinima_original_chunk_006 fuel constraintMinimaArrayAcc00600

theorem value_constraintMinima_original (fuel : Nat) :
    SourceJson.value (fuel + 117) (geometryChars00.drop 60487) =
      .ok (constraintMinimaArrayValue00, geometryChars00.drop 62654) := by
  exact (value_constraintMinima_open fuel).trans (constraintMinima_array_through_block_001 fuel)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 constraintMinima_block_001_complete"
  err.flush

#print axioms geometryChars00_constraintMinima_chunk_004_prefix
#print axioms geometryChars00_constraintMinima_chunk_004_split
#print axioms array_constraintMinima_chunk_004
#print axioms array_constraintMinima_original_chunk_004
#print axioms geometryChars00_constraintMinima_chunk_005_prefix
#print axioms geometryChars00_constraintMinima_chunk_005_split
#print axioms array_constraintMinima_chunk_005
#print axioms array_constraintMinima_original_chunk_005
#print axioms geometryChars00_constraintMinima_chunk_006_prefix
#print axioms geometryChars00_constraintMinima_chunk_006_split
#print axioms array_constraintMinima_chunk_006
#print axioms array_constraintMinima_original_chunk_006
#print axioms constraintMinima_array_through_block_001
#print axioms value_constraintMinima_original

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
