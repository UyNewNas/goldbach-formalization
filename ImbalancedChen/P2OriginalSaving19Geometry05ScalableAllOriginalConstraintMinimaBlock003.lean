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

namespace AllOriginalConstraintMinimaBlock003

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0024_before_reader"
  err.flush

noncomputable def chunk0024Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '7', '9', '/', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '2', '1', '4', '0', '7', '4', '9', '/', '1', '6', '8', '0', '0', '0', '0', '0', '0', '"', ',']
noncomputable def chunk0024Push00 (acc : List SourceJson) : List SourceJson :=
  (.str (String.ofList ['1', '2', '1', '4', '0', '7', '4', '9', '/', '1', '6', '8', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['2', '3', '4', '3', '7', '9', '/', '1', '0', '0', '0', '0', '0', '0'])) :: (acc))

theorem array_chunk0024 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 68) (SourceJson.white (chunk0024Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 66) (SourceJson.white tail) (chunk0024Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0024_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0025_before_reader"
  err.flush

noncomputable def chunk0025Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '3', '2', '8', '1', '4', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '7', '/', '2', '5', '6', '"', ',']
noncomputable def chunk0025Push00 (acc : List SourceJson) : List SourceJson :=
  (.str (String.ofList ['7', '/', '2', '5', '6'])) :: ((.str (String.ofList ['3', '2', '8', '1', '4', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0'])) :: (acc))

theorem array_chunk0025 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 66) (SourceJson.white (chunk0025Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 64) (SourceJson.white tail) (chunk0025Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0025_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0026_before_reader"
  err.flush

noncomputable def chunk0026Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '7', '3', '1', '/', '4', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '3', '2', '8', '1', '4', '1', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',']
noncomputable def chunk0026Push00 (acc : List SourceJson) : List SourceJson :=
  (.str (String.ofList ['3', '2', '8', '1', '4', '1', '/', '1', '2', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['2', '4', '8', '4', '7', '3', '1', '/', '4', '8', '0', '0', '0', '0', '0', '0'])) :: (acc))

theorem array_chunk0026 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 64) (SourceJson.white (chunk0026Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 62) (SourceJson.white tail) (chunk0026Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0026_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0027_before_reader"
  err.flush

noncomputable def chunk0027Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '5', '3', '9', '/', '4', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '/', '1', '2', '5', '0', '0', '0', '"', ',']
noncomputable def chunk0027Push00 (acc : List SourceJson) : List SourceJson :=
  (.str (String.ofList ['1', '/', '1', '2', '5', '0', '0', '0'])) :: ((.str (String.ofList ['2', '4', '8', '4', '5', '3', '9', '/', '4', '8', '0', '0', '0', '0', '0', '0'])) :: (acc))

theorem array_chunk0027 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 62) (SourceJson.white (chunk0027Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 60) (SourceJson.white tail) (chunk0027Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0027_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0028_before_reader"
  err.flush

noncomputable def chunk0028Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '6', '5', '4', '7', '6', '6', '3', '/', '9', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '3', '2', '8', '1', '4', '7', '/', '1', '0', '5', '0', '0', '0', '0', '0', '"', ',']
noncomputable def chunk0028Push00 (acc : List SourceJson) : List SourceJson :=
  (.str (String.ofList ['3', '2', '8', '1', '4', '7', '/', '1', '0', '5', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['1', '6', '5', '4', '7', '6', '6', '3', '/', '9', '6', '0', '0', '0', '0', '0', '0'])) :: (acc))

theorem array_chunk0028 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 60) (SourceJson.white (chunk0028Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 58) (SourceJson.white tail) (chunk0028Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0028_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0029_before_reader"
  err.flush

noncomputable def chunk0029Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '4', '1', '1', '/', '5', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '/', '2', '5', '0', '0', '0', '0', '"', ',']
noncomputable def chunk0029Push00 (acc : List SourceJson) : List SourceJson :=
  (.str (String.ofList ['1', '/', '2', '5', '0', '0', '0', '0'])) :: ((.str (String.ofList ['2', '4', '8', '4', '4', '1', '1', '/', '5', '6', '0', '0', '0', '0', '0', '0'])) :: (acc))

theorem array_chunk0029 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 58) (SourceJson.white (chunk0029Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 56) (SourceJson.white tail) (chunk0029Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0029_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0030_before_reader"
  err.flush

noncomputable def chunk0030Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '6', '5', '4', '7', '2', '7', '9', '/', '9', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '0', '"', ',']
noncomputable def chunk0030Push00 (acc : List SourceJson) : List SourceJson :=
  (.str (String.ofList ['0'])) :: ((.str (String.ofList ['1', '6', '5', '4', '7', '2', '7', '9', '/', '9', '6', '0', '0', '0', '0', '0', '0'])) :: (acc))

theorem array_chunk0030 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 56) (SourceJson.white (chunk0030Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 54) (SourceJson.white tail) (chunk0030Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0030_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0031_before_reader"
  err.flush

noncomputable def chunk0031Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '3', '3', '0', '9', '3', '7', '9', '/', '1', '9', '2', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '8', '7', '/', '2', '0', '0', '0', '0', '0', '0', '"', ',']
noncomputable def chunk0031Push00 (acc : List SourceJson) : List SourceJson :=
  (.str (String.ofList ['2', '3', '4', '3', '8', '7', '/', '2', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['3', '3', '0', '9', '3', '7', '9', '/', '1', '9', '2', '0', '0', '0', '0', '0'])) :: (acc))

theorem array_chunk0031 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 54) (SourceJson.white (chunk0031Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 52) (SourceJson.white tail) (chunk0031Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0031_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0024Chars00 ++ chunk0025Chars00 ++ chunk0026Chars00 ++ chunk0027Chars00 ++ chunk0028Chars00 ++ chunk0029Chars00 ++ chunk0030Chars00 ++ chunk0031Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0031Push00 (chunk0030Push00 (chunk0029Push00 (chunk0028Push00 (chunk0027Push00 (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc))))))))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 68) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 52) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0024Chars00 ++ (chunk0025Chars00 ++ (chunk0026Chars00 ++ (chunk0027Chars00 ++ (chunk0028Chars00 ++ (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail)))))))) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 68) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 68) (SourceJson.white (chunk0024Chars00 ++ (chunk0025Chars00 ++ (chunk0026Chars00 ++ (chunk0027Chars00 ++ (chunk0028Chars00 ++ (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail)))))))))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 68) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 66) (SourceJson.white (chunk0025Chars00 ++ (chunk0026Chars00 ++ (chunk0027Chars00 ++ (chunk0028Chars00 ++ (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail))))))))) (chunk0024Push00 (acc)) := array_chunk0024 fuel (chunk0025Chars00 ++ (chunk0026Chars00 ++ (chunk0027Chars00 ++ (chunk0028Chars00 ++ (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail)))))))) (acc)
    _ = SourceJson.array (fuel + 64) (SourceJson.white (chunk0026Chars00 ++ (chunk0027Chars00 ++ (chunk0028Chars00 ++ (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail)))))))) (chunk0025Push00 (chunk0024Push00 (acc))) := array_chunk0025 fuel (chunk0026Chars00 ++ (chunk0027Chars00 ++ (chunk0028Chars00 ++ (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail))))))) (chunk0024Push00 (acc))
    _ = SourceJson.array (fuel + 62) (SourceJson.white (chunk0027Chars00 ++ (chunk0028Chars00 ++ (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail))))))) (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc)))) := array_chunk0026 fuel (chunk0027Chars00 ++ (chunk0028Chars00 ++ (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail)))))) (chunk0025Push00 (chunk0024Push00 (acc)))
    _ = SourceJson.array (fuel + 60) (SourceJson.white (chunk0028Chars00 ++ (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail)))))) (chunk0027Push00 (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc))))) := array_chunk0027 fuel (chunk0028Chars00 ++ (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail))))) (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc))))
    _ = SourceJson.array (fuel + 58) (SourceJson.white (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail))))) (chunk0028Push00 (chunk0027Push00 (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc)))))) := array_chunk0028 fuel (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail)))) (chunk0027Push00 (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc)))))
    _ = SourceJson.array (fuel + 56) (SourceJson.white (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail)))) (chunk0029Push00 (chunk0028Push00 (chunk0027Push00 (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc))))))) := array_chunk0029 fuel (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail))) (chunk0028Push00 (chunk0027Push00 (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc))))))
    _ = SourceJson.array (fuel + 54) (SourceJson.white (chunk0031Chars00 ++ (tail))) (chunk0030Push00 (chunk0029Push00 (chunk0028Push00 (chunk0027Push00 (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc)))))))) := array_chunk0030 fuel (chunk0031Chars00 ++ (tail)) (chunk0029Push00 (chunk0028Push00 (chunk0027Push00 (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc)))))))
    _ = SourceJson.array (fuel + 52) (SourceJson.white tail) (blockPush acc) := array_chunk0031 fuel (tail) (chunk0030Push00 (chunk0029Push00 (chunk0028Push00 (chunk0027Push00 (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc))))))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 61915).take 355 = blockChars := by rfl

theorem block_original_split : sourceRest 61915 = blockChars ++ sourceRest 62270 := by
  calc
    sourceRest 61915 = (sourceRest 61915).take 355 ++ (sourceRest 61915).drop 355 :=
      (List.take_append_drop 355 (sourceRest 61915)).symm
    _ = blockChars ++ (sourceRest 61915).drop 355 :=
      congrArg (fun part => part ++ (sourceRest 61915).drop 355) block_original_prefix
    _ = blockChars ++ sourceRest 62270 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 61915 355)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 68) (SourceJson.white (sourceRest 61915)) acc =
      SourceJson.array (fuel + 52) (SourceJson.white (sourceRest 62270)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 68) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 62270) acc)

#print axioms array_chunk0024
#print axioms array_chunk0025
#print axioms array_chunk0026
#print axioms array_chunk0027
#print axioms array_chunk0028
#print axioms array_chunk0029
#print axioms array_chunk0030
#print axioms array_chunk0031
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end AllOriginalConstraintMinimaBlock003

end ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
