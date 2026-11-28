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

namespace AllOriginalConstraintMinimaBlock001

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0008_before_reader"
  err.flush

noncomputable def chunk0008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '7', '5', '/', '2', '7', '5', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '/', '5', '0', '0', '0', '0', '0', '"', ',']
noncomputable def chunk0008Push00 (acc : List SourceJson) : List SourceJson :=
  (.str (String.ofList ['1', '/', '5', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['7', '5', '/', '2', '7', '5', '2'])) :: (acc))

theorem array_chunk0008 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 100) (SourceJson.white (chunk0008Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 98) (SourceJson.white tail) (chunk0008Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0008_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0009_before_reader"
  err.flush

noncomputable def chunk0009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '0', '"', ',']
noncomputable def chunk0009Push00 (acc : List SourceJson) : List SourceJson :=
  (.str (String.ofList ['0'])) :: ((.str (String.ofList ['0'])) :: (acc))

theorem array_chunk0009 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 98) (SourceJson.white (chunk0009Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 96) (SourceJson.white tail) (chunk0009Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0009_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0010_before_reader"
  err.flush

noncomputable def chunk0010Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '2', '1', '4', '0', '8', '1', '3', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '5', '6', '3', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', ',']
noncomputable def chunk0010Push00 (acc : List SourceJson) : List SourceJson :=
  (.str (String.ofList ['5', '1', '0', '9', '5', '6', '3', '/', '3', '6', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['1', '2', '1', '4', '0', '8', '1', '3', '/', '3', '6', '0', '0', '0', '0', '0', '0'])) :: (acc))

theorem array_chunk0010 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 96) (SourceJson.white (chunk0010Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 94) (SourceJson.white tail) (chunk0010Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0010_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0011_before_reader"
  err.flush

noncomputable def chunk0011Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '8', '1', '7', '2', '1', '8', '3', '/', '6', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '3', '1', '4', '0', '7', '1', '7', '/', '1', '8', '0', '0', '0', '0', '0', '0', '"', ',']
noncomputable def chunk0011Push00 (acc : List SourceJson) : List SourceJson :=
  (.str (String.ofList ['3', '1', '4', '0', '7', '1', '7', '/', '1', '8', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['1', '8', '1', '7', '2', '1', '8', '3', '/', '6', '8', '0', '0', '0', '0', '0', '0'])) :: (acc))

theorem array_chunk0011 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 94) (SourceJson.white (chunk0011Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 92) (SourceJson.white tail) (chunk0011Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0011_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0012_before_reader"
  err.flush

noncomputable def chunk0012Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '2', '7', '6', '5', '7', '7', '3', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '2', '6', '7', '1', '9', '2', '7', '/', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',']
noncomputable def chunk0012Push00 (acc : List SourceJson) : List SourceJson :=
  (.str (String.ofList ['2', '6', '7', '1', '9', '2', '7', '/', '2', '0', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['2', '7', '6', '5', '7', '7', '3', '/', '3', '6', '0', '0', '0', '0', '0', '0'])) :: (acc))

theorem array_chunk0012 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 92) (SourceJson.white (chunk0012Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 90) (SourceJson.white tail) (chunk0012Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0012_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0013_before_reader"
  err.flush

noncomputable def chunk0013Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '4', '5', '3', '1', '6', '9', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '4', '0', '6', '3', '/', '1', '5', '0', '0', '0', '0', '"', ',']
noncomputable def chunk0013Push00 (acc : List SourceJson) : List SourceJson :=
  (.str (String.ofList ['1', '4', '0', '6', '3', '/', '1', '5', '0', '0', '0', '0'])) :: ((.str (String.ofList ['1', '4', '5', '3', '1', '6', '9', '/', '1', '2', '0', '0', '0', '0', '0', '0'])) :: (acc))

theorem array_chunk0013 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 90) (SourceJson.white (chunk0013Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 88) (SourceJson.white tail) (chunk0013Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0013_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0014_before_reader"
  err.flush

noncomputable def chunk0014Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '4', '8', '4', '3', '8', '7', '/', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '4', '5', '3', '1', '6', '1', '/', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',']
noncomputable def chunk0014Push00 (acc : List SourceJson) : List SourceJson :=
  (.str (String.ofList ['1', '4', '5', '3', '1', '6', '1', '/', '2', '0', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['4', '8', '4', '3', '8', '7', '/', '5', '0', '0', '0', '0', '0', '0'])) :: (acc))

theorem array_chunk0014 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 88) (SourceJson.white (chunk0014Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 86) (SourceJson.white tail) (chunk0014Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0014_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0015_before_reader"
  err.flush

noncomputable def chunk0015Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '"', '1', '2', '0', '3', '1', '6', '9', '/', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', '"', '3', '5', '9', '3', '9', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',']
noncomputable def chunk0015Push00 (acc : List SourceJson) : List SourceJson :=
  (.str (String.ofList ['3', '5', '9', '3', '9', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0'])) :: ((.str (String.ofList ['1', '2', '0', '3', '1', '6', '9', '/', '2', '0', '0', '0', '0', '0', '0', '0'])) :: (acc))

theorem array_chunk0015 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 86) (SourceJson.white (chunk0015Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 84) (SourceJson.white tail) (chunk0015Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0015_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0008Chars00 ++ chunk0009Chars00 ++ chunk0010Chars00 ++ chunk0011Chars00 ++ chunk0012Chars00 ++ chunk0013Chars00 ++ chunk0014Chars00 ++ chunk0015Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0015Push00 (chunk0014Push00 (chunk0013Push00 (chunk0012Push00 (chunk0011Push00 (chunk0010Push00 (chunk0009Push00 (chunk0008Push00 (acc))))))))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 100) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 84) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0008Chars00 ++ (chunk0009Chars00 ++ (chunk0010Chars00 ++ (chunk0011Chars00 ++ (chunk0012Chars00 ++ (chunk0013Chars00 ++ (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail)))))))) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 100) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 100) (SourceJson.white (chunk0008Chars00 ++ (chunk0009Chars00 ++ (chunk0010Chars00 ++ (chunk0011Chars00 ++ (chunk0012Chars00 ++ (chunk0013Chars00 ++ (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail)))))))))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 100) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 98) (SourceJson.white (chunk0009Chars00 ++ (chunk0010Chars00 ++ (chunk0011Chars00 ++ (chunk0012Chars00 ++ (chunk0013Chars00 ++ (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail))))))))) (chunk0008Push00 (acc)) := array_chunk0008 fuel (chunk0009Chars00 ++ (chunk0010Chars00 ++ (chunk0011Chars00 ++ (chunk0012Chars00 ++ (chunk0013Chars00 ++ (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail)))))))) (acc)
    _ = SourceJson.array (fuel + 96) (SourceJson.white (chunk0010Chars00 ++ (chunk0011Chars00 ++ (chunk0012Chars00 ++ (chunk0013Chars00 ++ (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail)))))))) (chunk0009Push00 (chunk0008Push00 (acc))) := array_chunk0009 fuel (chunk0010Chars00 ++ (chunk0011Chars00 ++ (chunk0012Chars00 ++ (chunk0013Chars00 ++ (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail))))))) (chunk0008Push00 (acc))
    _ = SourceJson.array (fuel + 94) (SourceJson.white (chunk0011Chars00 ++ (chunk0012Chars00 ++ (chunk0013Chars00 ++ (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail))))))) (chunk0010Push00 (chunk0009Push00 (chunk0008Push00 (acc)))) := array_chunk0010 fuel (chunk0011Chars00 ++ (chunk0012Chars00 ++ (chunk0013Chars00 ++ (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail)))))) (chunk0009Push00 (chunk0008Push00 (acc)))
    _ = SourceJson.array (fuel + 92) (SourceJson.white (chunk0012Chars00 ++ (chunk0013Chars00 ++ (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail)))))) (chunk0011Push00 (chunk0010Push00 (chunk0009Push00 (chunk0008Push00 (acc))))) := array_chunk0011 fuel (chunk0012Chars00 ++ (chunk0013Chars00 ++ (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail))))) (chunk0010Push00 (chunk0009Push00 (chunk0008Push00 (acc))))
    _ = SourceJson.array (fuel + 90) (SourceJson.white (chunk0013Chars00 ++ (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail))))) (chunk0012Push00 (chunk0011Push00 (chunk0010Push00 (chunk0009Push00 (chunk0008Push00 (acc)))))) := array_chunk0012 fuel (chunk0013Chars00 ++ (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail)))) (chunk0011Push00 (chunk0010Push00 (chunk0009Push00 (chunk0008Push00 (acc)))))
    _ = SourceJson.array (fuel + 88) (SourceJson.white (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail)))) (chunk0013Push00 (chunk0012Push00 (chunk0011Push00 (chunk0010Push00 (chunk0009Push00 (chunk0008Push00 (acc))))))) := array_chunk0013 fuel (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail))) (chunk0012Push00 (chunk0011Push00 (chunk0010Push00 (chunk0009Push00 (chunk0008Push00 (acc))))))
    _ = SourceJson.array (fuel + 86) (SourceJson.white (chunk0015Chars00 ++ (tail))) (chunk0014Push00 (chunk0013Push00 (chunk0012Push00 (chunk0011Push00 (chunk0010Push00 (chunk0009Push00 (chunk0008Push00 (acc)))))))) := array_chunk0014 fuel (chunk0015Chars00 ++ (tail)) (chunk0013Push00 (chunk0012Push00 (chunk0011Push00 (chunk0010Push00 (chunk0009Push00 (chunk0008Push00 (acc)))))))
    _ = SourceJson.array (fuel + 84) (SourceJson.white tail) (blockPush acc) := array_chunk0015 fuel (tail) (chunk0014Push00 (chunk0013Push00 (chunk0012Push00 (chunk0011Push00 (chunk0010Push00 (chunk0009Push00 (chunk0008Push00 (acc))))))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 64278).take 348 = blockChars := by rfl

theorem block_original_split : sourceRest 64278 = blockChars ++ sourceRest 64626 := by
  calc
    sourceRest 64278 = (sourceRest 64278).take 348 ++ (sourceRest 64278).drop 348 :=
      (List.take_append_drop 348 (sourceRest 64278)).symm
    _ = blockChars ++ (sourceRest 64278).drop 348 :=
      congrArg (fun part => part ++ (sourceRest 64278).drop 348) block_original_prefix
    _ = blockChars ++ sourceRest 64626 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 64278 348)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 100) (SourceJson.white (sourceRest 64278)) acc =
      SourceJson.array (fuel + 84) (SourceJson.white (sourceRest 64626)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 100) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 64626) acc)

#print axioms array_chunk0008
#print axioms array_chunk0009
#print axioms array_chunk0010
#print axioms array_chunk0011
#print axioms array_chunk0012
#print axioms array_chunk0013
#print axioms array_chunk0014
#print axioms array_chunk0015
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end AllOriginalConstraintMinimaBlock001

end ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing
