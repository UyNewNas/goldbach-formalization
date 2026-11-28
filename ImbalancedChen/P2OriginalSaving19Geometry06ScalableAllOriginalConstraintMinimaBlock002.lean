import ImbalancedChen.P2OriginalSaving19Geometry06ScalableInput

/-! Original all_original_constraint_minima grouped chunk transitions, including exact compact-input binding.
The original packed input, original parser and original decoder are unchanged.
This is a source-only candidate until normal, kernel and full-owned checks pass. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing
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

noncomputable def chunk0016Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '7', '9', '6', '9', '0', '3', '/', '1', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '7', '9', '6', '9', '0', '3', '/', '1', '8', '0', '0', '0', '0', '0', '0', '"', ',']
noncomputable def chunk0016Push00 (acc : List SourceJson) : List SourceJson :=
  (.str (String.ofList ['7', '9', '6', '9', '0', '3', '/', '1', '8', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['7', '9', '6', '9', '0', '3', '/', '1', '8', '0', '0', '0', '0', '0', '0'])) :: (acc))

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

noncomputable def chunk0018Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '8', '2', '9', '6', '8', '4', '7', '/', '4', '0', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '0', '"', ',']
noncomputable def chunk0018Push00 (acc : List SourceJson) : List SourceJson :=
  (.str (String.ofList ['0'])) :: ((.str (String.ofList ['1', '8', '2', '9', '6', '8', '4', '7', '/', '4', '0', '4', '0', '0', '0', '0', '0', '0'])) :: (acc))

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

noncomputable def chunk0019Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '2', '5', '/', '2', '7', '5', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '0', '"', ',']
noncomputable def chunk0019Push00 (acc : List SourceJson) : List SourceJson :=
  (.str (String.ofList ['0'])) :: ((.str (String.ofList ['1', '2', '5', '/', '2', '7', '5', '2'])) :: (acc))

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

noncomputable def chunk0020Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '9', '0', '3', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',']
noncomputable def chunk0020Push00 (acc : List SourceJson) : List SourceJson :=
  (.str (String.ofList ['1', '1', '7', '1', '9', '0', '3', '/', '1', '0', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['0'])) :: (acc))

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

noncomputable def chunk0021Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '4', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '4', '8', '4', '3', '6', '7', '/', '5', '5', '0', '0', '0', '0', '0', '0', '"', ',']
noncomputable def chunk0021Push00 (acc : List SourceJson) : List SourceJson :=
  (.str (String.ofList ['4', '8', '4', '3', '6', '7', '/', '5', '5', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '4', '4', '0', '0', '0', '0', '0', '0'])) :: (acc))

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

noncomputable def chunk0022Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '7', '5', '/', '6', '8', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '4', '8', '4', '3', '6', '7', '/', '5', '5', '0', '0', '0', '0', '0', '0', '"', ',']
noncomputable def chunk0022Push00 (acc : List SourceJson) : List SourceJson :=
  (.str (String.ofList ['4', '8', '4', '3', '6', '7', '/', '5', '5', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['7', '5', '/', '6', '8', '8'])) :: (acc))

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

noncomputable def chunk0023Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '7', '5', '/', '6', '8', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '9', '4', '3', '/', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',']
noncomputable def chunk0023Push00 (acc : List SourceJson) : List SourceJson :=
  (.str (String.ofList ['1', '1', '7', '1', '9', '4', '3', '/', '2', '0', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['7', '5', '/', '6', '8', '8'])) :: (acc))

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
    (sourceRest 64626).take 308 = blockChars := by rfl

theorem block_original_split : sourceRest 64626 = blockChars ++ sourceRest 64934 := by
  calc
    sourceRest 64626 = (sourceRest 64626).take 308 ++ (sourceRest 64626).drop 308 :=
      (List.take_append_drop 308 (sourceRest 64626)).symm
    _ = blockChars ++ (sourceRest 64626).drop 308 :=
      congrArg (fun part => part ++ (sourceRest 64626).drop 308) block_original_prefix
    _ = blockChars ++ sourceRest 64934 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 64626 308)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 84) (SourceJson.white (sourceRest 64626)) acc =
      SourceJson.array (fuel + 68) (SourceJson.white (sourceRest 64934)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 84) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 64934) acc)

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

end ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing
