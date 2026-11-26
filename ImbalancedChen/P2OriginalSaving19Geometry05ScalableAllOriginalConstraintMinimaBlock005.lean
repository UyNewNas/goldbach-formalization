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

namespace AllOriginalConstraintMinimaBlock005

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0040_before_reader"
  err.flush

noncomputable def chunk0040Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '9', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '6', '3', '4', '3', '7', '9', '/', '1', '1', '2', '0', '0', '0', '0', '0', '"', ',']
noncomputable def chunk0040Push00 (acc : List SourceJson) : List SourceJson :=
  (.str (String.ofList ['6', '3', '4', '3', '7', '9', '/', '1', '1', '2', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '4', '0', '0', '0', '0', '0', '0'])) :: (acc))

theorem array_chunk0040 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 36) (SourceJson.white (chunk0040Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 34) (SourceJson.white tail) (chunk0040Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0040_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0041_before_reader"
  err.flush

noncomputable def chunk0041Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '8', '4', '8', '4', '2', '5', '1', '/', '6', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',']
noncomputable def chunk0041Push00 (acc : List SourceJson) : List SourceJson :=
  (.str (String.ofList ['8', '4', '8', '4', '2', '5', '1', '/', '6', '8', '0', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['0'])) :: (acc))

theorem array_chunk0041 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 34) (SourceJson.white (chunk0041Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 32) (SourceJson.white tail) (chunk0041Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0041_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0042_before_reader"
  err.flush

noncomputable def chunk0042Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '5', '3', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '3', '2', '8', '1', '4', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',']
noncomputable def chunk0042Push00 (acc : List SourceJson) : List SourceJson :=
  (.str (String.ofList ['3', '2', '8', '1', '4', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['2', '4', '8', '4', '5', '3', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0'])) :: (acc))

theorem array_chunk0042 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 32) (SourceJson.white (chunk0042Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 30) (SourceJson.white tail) (chunk0042Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0042_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0043_before_reader"
  err.flush

noncomputable def chunk0043Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '4', '4', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '7', '3', '1', '/', '4', '8', '0', '0', '0', '0', '0', '0', '"', ',']
noncomputable def chunk0043Push00 (acc : List SourceJson) : List SourceJson :=
  (.str (String.ofList ['2', '4', '8', '4', '7', '3', '1', '/', '4', '8', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['2', '4', '8', '4', '4', '4', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0'])) :: (acc))

theorem array_chunk0043 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 30) (SourceJson.white (chunk0043Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 28) (SourceJson.white tail) (chunk0043Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0043_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0044_before_reader"
  err.flush

noncomputable def chunk0044Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '7', '1', '7', '2', '1', '1', '9', '/', '3', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '0', '9', '3', '8', '7', '/', '7', '0', '0', '0', '0', '0', '0', '"', ',']
noncomputable def chunk0044Push00 (acc : List SourceJson) : List SourceJson :=
  (.str (String.ofList ['1', '0', '9', '3', '8', '7', '/', '7', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['7', '1', '7', '2', '1', '1', '9', '/', '3', '2', '0', '0', '0', '0', '0', '0'])) :: (acc))

theorem array_chunk0044 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 28) (SourceJson.white (chunk0044Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 26) (SourceJson.white tail) (chunk0044Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0044_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0045_before_reader"
  err.flush

noncomputable def chunk0045Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '4', '1', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '4', '9', '6', '9', '2', '7', '/', '1', '1', '2', '0', '0', '0', '0', '0', '"', ',']
noncomputable def chunk0045Push00 (acc : List SourceJson) : List SourceJson :=
  (.str (String.ofList ['4', '9', '6', '9', '2', '7', '/', '1', '1', '2', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['2', '4', '8', '4', '4', '1', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0'])) :: (acc))

theorem array_chunk0045 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 26) (SourceJson.white (chunk0045Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 24) (SourceJson.white tail) (chunk0045Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0045_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0046_before_reader"
  err.flush

noncomputable def chunk0046Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '7', '1', '7', '1', '9', '9', '1', '/', '3', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '5', '3', '9', '/', '1', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',']
noncomputable def chunk0046Push00 (acc : List SourceJson) : List SourceJson :=
  (.str (String.ofList ['5', '1', '0', '9', '5', '3', '9', '/', '1', '2', '0', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['7', '1', '7', '1', '9', '9', '1', '/', '3', '2', '0', '0', '0', '0', '0', '0'])) :: (acc))

theorem array_chunk0046 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 24) (SourceJson.white (chunk0046Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 22) (SourceJson.white tail) (chunk0046Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0046_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0047_before_reader"
  err.flush

noncomputable def chunk0047Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '7', '1', '7', '1', '8', '6', '3', '/', '3', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '6', '5', '4', '7', '2', '7', '9', '/', '9', '6', '0', '0', '0', '0', '0', '0', '"', ',']
noncomputable def chunk0047Push00 (acc : List SourceJson) : List SourceJson :=
  (.str (String.ofList ['1', '6', '5', '4', '7', '2', '7', '9', '/', '9', '6', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['7', '1', '7', '1', '8', '6', '3', '/', '3', '2', '0', '0', '0', '0', '0', '0'])) :: (acc))

theorem array_chunk0047 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 22) (SourceJson.white (chunk0047Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 20) (SourceJson.white tail) (chunk0047Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0047_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0040Chars00 ++ chunk0041Chars00 ++ chunk0042Chars00 ++ chunk0043Chars00 ++ chunk0044Chars00 ++ chunk0045Chars00 ++ chunk0046Chars00 ++ chunk0047Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0047Push00 (chunk0046Push00 (chunk0045Push00 (chunk0044Push00 (chunk0043Push00 (chunk0042Push00 (chunk0041Push00 (chunk0040Push00 (acc))))))))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 36) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 20) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0040Chars00 ++ (chunk0041Chars00 ++ (chunk0042Chars00 ++ (chunk0043Chars00 ++ (chunk0044Chars00 ++ (chunk0045Chars00 ++ (chunk0046Chars00 ++ (chunk0047Chars00 ++ (tail)))))))) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 36) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 36) (SourceJson.white (chunk0040Chars00 ++ (chunk0041Chars00 ++ (chunk0042Chars00 ++ (chunk0043Chars00 ++ (chunk0044Chars00 ++ (chunk0045Chars00 ++ (chunk0046Chars00 ++ (chunk0047Chars00 ++ (tail)))))))))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 36) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 34) (SourceJson.white (chunk0041Chars00 ++ (chunk0042Chars00 ++ (chunk0043Chars00 ++ (chunk0044Chars00 ++ (chunk0045Chars00 ++ (chunk0046Chars00 ++ (chunk0047Chars00 ++ (tail))))))))) (chunk0040Push00 (acc)) := array_chunk0040 fuel (chunk0041Chars00 ++ (chunk0042Chars00 ++ (chunk0043Chars00 ++ (chunk0044Chars00 ++ (chunk0045Chars00 ++ (chunk0046Chars00 ++ (chunk0047Chars00 ++ (tail)))))))) (acc)
    _ = SourceJson.array (fuel + 32) (SourceJson.white (chunk0042Chars00 ++ (chunk0043Chars00 ++ (chunk0044Chars00 ++ (chunk0045Chars00 ++ (chunk0046Chars00 ++ (chunk0047Chars00 ++ (tail)))))))) (chunk0041Push00 (chunk0040Push00 (acc))) := array_chunk0041 fuel (chunk0042Chars00 ++ (chunk0043Chars00 ++ (chunk0044Chars00 ++ (chunk0045Chars00 ++ (chunk0046Chars00 ++ (chunk0047Chars00 ++ (tail))))))) (chunk0040Push00 (acc))
    _ = SourceJson.array (fuel + 30) (SourceJson.white (chunk0043Chars00 ++ (chunk0044Chars00 ++ (chunk0045Chars00 ++ (chunk0046Chars00 ++ (chunk0047Chars00 ++ (tail))))))) (chunk0042Push00 (chunk0041Push00 (chunk0040Push00 (acc)))) := array_chunk0042 fuel (chunk0043Chars00 ++ (chunk0044Chars00 ++ (chunk0045Chars00 ++ (chunk0046Chars00 ++ (chunk0047Chars00 ++ (tail)))))) (chunk0041Push00 (chunk0040Push00 (acc)))
    _ = SourceJson.array (fuel + 28) (SourceJson.white (chunk0044Chars00 ++ (chunk0045Chars00 ++ (chunk0046Chars00 ++ (chunk0047Chars00 ++ (tail)))))) (chunk0043Push00 (chunk0042Push00 (chunk0041Push00 (chunk0040Push00 (acc))))) := array_chunk0043 fuel (chunk0044Chars00 ++ (chunk0045Chars00 ++ (chunk0046Chars00 ++ (chunk0047Chars00 ++ (tail))))) (chunk0042Push00 (chunk0041Push00 (chunk0040Push00 (acc))))
    _ = SourceJson.array (fuel + 26) (SourceJson.white (chunk0045Chars00 ++ (chunk0046Chars00 ++ (chunk0047Chars00 ++ (tail))))) (chunk0044Push00 (chunk0043Push00 (chunk0042Push00 (chunk0041Push00 (chunk0040Push00 (acc)))))) := array_chunk0044 fuel (chunk0045Chars00 ++ (chunk0046Chars00 ++ (chunk0047Chars00 ++ (tail)))) (chunk0043Push00 (chunk0042Push00 (chunk0041Push00 (chunk0040Push00 (acc)))))
    _ = SourceJson.array (fuel + 24) (SourceJson.white (chunk0046Chars00 ++ (chunk0047Chars00 ++ (tail)))) (chunk0045Push00 (chunk0044Push00 (chunk0043Push00 (chunk0042Push00 (chunk0041Push00 (chunk0040Push00 (acc))))))) := array_chunk0045 fuel (chunk0046Chars00 ++ (chunk0047Chars00 ++ (tail))) (chunk0044Push00 (chunk0043Push00 (chunk0042Push00 (chunk0041Push00 (chunk0040Push00 (acc))))))
    _ = SourceJson.array (fuel + 22) (SourceJson.white (chunk0047Chars00 ++ (tail))) (chunk0046Push00 (chunk0045Push00 (chunk0044Push00 (chunk0043Push00 (chunk0042Push00 (chunk0041Push00 (chunk0040Push00 (acc)))))))) := array_chunk0046 fuel (chunk0047Chars00 ++ (tail)) (chunk0045Push00 (chunk0044Push00 (chunk0043Push00 (chunk0042Push00 (chunk0041Push00 (chunk0040Push00 (acc)))))))
    _ = SourceJson.array (fuel + 20) (SourceJson.white tail) (blockPush acc) := array_chunk0047 fuel (tail) (chunk0046Push00 (chunk0045Push00 (chunk0044Push00 (chunk0043Push00 (chunk0042Push00 (chunk0041Push00 (chunk0040Push00 (acc))))))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 62614).take 382 = blockChars := by rfl

theorem block_original_split : sourceRest 62614 = blockChars ++ sourceRest 62996 := by
  calc
    sourceRest 62614 = (sourceRest 62614).take 382 ++ (sourceRest 62614).drop 382 :=
      (List.take_append_drop 382 (sourceRest 62614)).symm
    _ = blockChars ++ (sourceRest 62614).drop 382 :=
      congrArg (fun part => part ++ (sourceRest 62614).drop 382) block_original_prefix
    _ = blockChars ++ sourceRest 62996 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 62614 382)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 36) (SourceJson.white (sourceRest 62614)) acc =
      SourceJson.array (fuel + 20) (SourceJson.white (sourceRest 62996)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 36) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 62996) acc)

#print axioms array_chunk0040
#print axioms array_chunk0041
#print axioms array_chunk0042
#print axioms array_chunk0043
#print axioms array_chunk0044
#print axioms array_chunk0045
#print axioms array_chunk0046
#print axioms array_chunk0047
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end AllOriginalConstraintMinimaBlock005

end ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
