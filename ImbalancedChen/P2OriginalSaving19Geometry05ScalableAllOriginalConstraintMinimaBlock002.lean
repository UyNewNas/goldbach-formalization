import ImbalancedChen.P2OriginalSaving19Geometry05ScalableInput

/-! Original all_original_constraint_minima grouped chunk transitions, including exact compact-input binding.
The original packed input, original parser and original decoder are unchanged.
This is a source-only candidate until normal, kernel and full-owned checks pass. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

namespace AllOriginalConstraintMinimaBlock002

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0016_before_reader"
  err.flush

noncomputable def chunk0016Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '3', '1', '8', '7', '9', '/', '7', '2', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '3', '1', '8', '7', '9', '/', '7', '2', '0', '0', '0', '0', '"', ',']
noncomputable def chunk0016Push00 (acc : List SourceJson) : List SourceJson :=
  (.str (String.ofList ['3', '1', '8', '7', '9', '/', '7', '2', '0', '0', '0', '0'])) :: ((.str (String.ofList ['3', '1', '8', '7', '9', '/', '7', '2', '0', '0', '0', '0'])) :: (acc))

theorem array_chunk0016 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 84) (SourceJson.white (chunk0016Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 82) (SourceJson.white tail) (chunk0016Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0016_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0017_before_reader"
  err.flush

noncomputable def chunk0017Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '7', '9', '/', '7', '2', '0', '0', '0', '0', '0', '"', ',']
noncomputable def chunk0017Push00 (acc : List SourceJson) : List SourceJson :=
  (.str (String.ofList ['2', '3', '4', '3', '7', '9', '/', '7', '2', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['0'])) :: (acc))

theorem array_chunk0017 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 82) (SourceJson.white (chunk0017Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 80) (SourceJson.white tail) (chunk0017Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0017_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0018_before_reader"
  err.flush

noncomputable def chunk0018Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '3', '1', '4', '5', '3', '0', '4', '1', '/', '6', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '/', '2', '5', '0', '0', '0', '0', '"', ',']
noncomputable def chunk0018Push00 (acc : List SourceJson) : List SourceJson :=
  (.str (String.ofList ['1', '/', '2', '5', '0', '0', '0', '0'])) :: ((.str (String.ofList ['3', '1', '4', '5', '3', '0', '4', '1', '/', '6', '8', '0', '0', '0', '0', '0', '0', '0'])) :: (acc))

theorem array_chunk0018 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 80) (SourceJson.white (chunk0018Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 78) (SourceJson.white tail) (chunk0018Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0018_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0019_before_reader"
  err.flush

noncomputable def chunk0019Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '0', '"', ',']
noncomputable def chunk0019Push00 (acc : List SourceJson) : List SourceJson :=
  (.str (String.ofList ['0'])) :: ((.str (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0'])) :: (acc))

theorem array_chunk0019 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 78) (SourceJson.white (chunk0019Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 76) (SourceJson.white tail) (chunk0019Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0019_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0020_before_reader"
  err.flush

noncomputable def chunk0020Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '8', '7', '/', '2', '0', '0', '0', '0', '0', '0', '"', ',']
noncomputable def chunk0020Push00 (acc : List SourceJson) : List SourceJson :=
  (.str (String.ofList ['2', '3', '4', '3', '8', '7', '/', '2', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['0'])) :: (acc))

theorem array_chunk0020 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 76) (SourceJson.white (chunk0020Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 74) (SourceJson.white tail) (chunk0020Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0020_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0021_before_reader"
  err.flush

noncomputable def chunk0021Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '6', '3', '4', '3', '7', '9', '/', '1', '1', '2', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '8', '4', '8', '4', '2', '5', '1', '/', '6', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',']
noncomputable def chunk0021Push00 (acc : List SourceJson) : List SourceJson :=
  (.str (String.ofList ['8', '4', '8', '4', '2', '5', '1', '/', '6', '8', '0', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['6', '3', '4', '3', '7', '9', '/', '1', '1', '2', '0', '0', '0', '0', '0'])) :: (acc))

theorem array_chunk0021 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 74) (SourceJson.white (chunk0021Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 72) (SourceJson.white tail) (chunk0021Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0021_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0022_before_reader"
  err.flush

noncomputable def chunk0022Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '7', '9', '/', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '3', '2', '8', '1', '4', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',']
noncomputable def chunk0022Push00 (acc : List SourceJson) : List SourceJson :=
  (.str (String.ofList ['3', '2', '8', '1', '4', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['2', '3', '4', '3', '7', '9', '/', '2', '0', '0', '0', '0', '0', '0'])) :: (acc))

theorem array_chunk0022 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 72) (SourceJson.white (chunk0022Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 70) (SourceJson.white tail) (chunk0022Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0022_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0023_before_reader"
  err.flush

noncomputable def chunk0023Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '7', '1', '7', '1', '8', '6', '3', '/', '6', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '4', '6', '8', '7', '9', '/', '8', '0', '0', '0', '0', '0', '"', ',']
noncomputable def chunk0023Push00 (acc : List SourceJson) : List SourceJson :=
  (.str (String.ofList ['4', '6', '8', '7', '9', '/', '8', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['7', '1', '7', '1', '8', '6', '3', '/', '6', '4', '0', '0', '0', '0', '0', '0'])) :: (acc))

theorem array_chunk0023 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 70) (SourceJson.white (chunk0023Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 68) (SourceJson.white tail) (chunk0023Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0023_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0016Chars00 ++ chunk0017Chars00 ++ chunk0018Chars00 ++ chunk0019Chars00 ++ chunk0020Chars00 ++ chunk0021Chars00 ++ chunk0022Chars00 ++ chunk0023Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0023Push00 (chunk0022Push00 (chunk0021Push00 (chunk0020Push00 (chunk0019Push00 (chunk0018Push00 (chunk0017Push00 (chunk0016Push00 (acc))))))))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 84) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 68) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0016Chars00 ++ (chunk0017Chars00 ++ (chunk0018Chars00 ++ (chunk0019Chars00 ++ (chunk0020Chars00 ++ (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail)))))))) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 84) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 84) (SourceJson.white (chunk0016Chars00 ++ (chunk0017Chars00 ++ (chunk0018Chars00 ++ (chunk0019Chars00 ++ (chunk0020Chars00 ++ (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail)))))))))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 84) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 82) (SourceJson.white (chunk0017Chars00 ++ (chunk0018Chars00 ++ (chunk0019Chars00 ++ (chunk0020Chars00 ++ (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail))))))))) (chunk0016Push00 (acc)) := array_chunk0016 fuel (chunk0017Chars00 ++ (chunk0018Chars00 ++ (chunk0019Chars00 ++ (chunk0020Chars00 ++ (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail)))))))) (acc)
    _ = SourceJson.array (fuel + 80) (SourceJson.white (chunk0018Chars00 ++ (chunk0019Chars00 ++ (chunk0020Chars00 ++ (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail)))))))) (chunk0017Push00 (chunk0016Push00 (acc))) := array_chunk0017 fuel (chunk0018Chars00 ++ (chunk0019Chars00 ++ (chunk0020Chars00 ++ (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail))))))) (chunk0016Push00 (acc))
    _ = SourceJson.array (fuel + 78) (SourceJson.white (chunk0019Chars00 ++ (chunk0020Chars00 ++ (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail))))))) (chunk0018Push00 (chunk0017Push00 (chunk0016Push00 (acc)))) := array_chunk0018 fuel (chunk0019Chars00 ++ (chunk0020Chars00 ++ (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail)))))) (chunk0017Push00 (chunk0016Push00 (acc)))
    _ = SourceJson.array (fuel + 76) (SourceJson.white (chunk0020Chars00 ++ (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail)))))) (chunk0019Push00 (chunk0018Push00 (chunk0017Push00 (chunk0016Push00 (acc))))) := array_chunk0019 fuel (chunk0020Chars00 ++ (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail))))) (chunk0018Push00 (chunk0017Push00 (chunk0016Push00 (acc))))
    _ = SourceJson.array (fuel + 74) (SourceJson.white (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail))))) (chunk0020Push00 (chunk0019Push00 (chunk0018Push00 (chunk0017Push00 (chunk0016Push00 (acc)))))) := array_chunk0020 fuel (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail)))) (chunk0019Push00 (chunk0018Push00 (chunk0017Push00 (chunk0016Push00 (acc)))))
    _ = SourceJson.array (fuel + 72) (SourceJson.white (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail)))) (chunk0021Push00 (chunk0020Push00 (chunk0019Push00 (chunk0018Push00 (chunk0017Push00 (chunk0016Push00 (acc))))))) := array_chunk0021 fuel (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail))) (chunk0020Push00 (chunk0019Push00 (chunk0018Push00 (chunk0017Push00 (chunk0016Push00 (acc))))))
    _ = SourceJson.array (fuel + 70) (SourceJson.white (chunk0023Chars00 ++ (tail))) (chunk0022Push00 (chunk0021Push00 (chunk0020Push00 (chunk0019Push00 (chunk0018Push00 (chunk0017Push00 (chunk0016Push00 (acc)))))))) := array_chunk0022 fuel (chunk0023Chars00 ++ (tail)) (chunk0021Push00 (chunk0020Push00 (chunk0019Push00 (chunk0018Push00 (chunk0017Push00 (chunk0016Push00 (acc)))))))
    _ = SourceJson.array (fuel + 68) (SourceJson.white tail) (blockPush acc) := array_chunk0023 fuel (tail) (chunk0022Push00 (chunk0021Push00 (chunk0020Push00 (chunk0019Push00 (chunk0018Push00 (chunk0017Push00 (chunk0016Push00 (acc))))))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 61585).take 330 = blockChars := by rfl

theorem block_original_split : sourceRest 61585 = blockChars ++ sourceRest 61915 := by
  calc
    sourceRest 61585 = (sourceRest 61585).take 330 ++ (sourceRest 61585).drop 330 :=
      (List.take_append_drop 330 (sourceRest 61585)).symm
    _ = blockChars ++ (sourceRest 61585).drop 330 :=
      congrArg (fun part => part ++ (sourceRest 61585).drop 330) block_original_prefix
    _ = blockChars ++ sourceRest 61915 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 61585 330)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 84) (SourceJson.white (sourceRest 61585)) acc =
      SourceJson.array (fuel + 68) (SourceJson.white (sourceRest 61915)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 84) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 61915) acc)

#print axioms array_chunk0016
#print axioms array_chunk0017
#print axioms array_chunk0018
#print axioms array_chunk0019
#print axioms array_chunk0020
#print axioms array_chunk0021
#print axioms array_chunk0022
#print axioms array_chunk0023
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end AllOriginalConstraintMinimaBlock002

end ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
