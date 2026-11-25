import ImbalancedChen.P2OriginalSaving19Geometry01DirectInput

/-! Original face_ledger grouped chunk transitions, including exact compact-input binding.
Original-reader equations and exact production packed-input slices are checked
in Lean. No whole-cell parse or typed decoding claim is made by this pilot. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

namespace FaceLedgerBlock012

noncomputable def fragment0198215Acc00000 : List SourceJson := []

noncomputable def fragment0198215Chunk000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0198215Chunk000Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '6']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '8']), .number (String.ofList ['3', '2']), .number (String.ofList ['3', '4'])]) :: ((.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '3']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '9'])]) :: (acc))

theorem array_fragment0198215_chunk_000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 23) (SourceJson.white (fragment0198215Chunk000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 21) (SourceJson.white tail) (fragment0198215Chunk000Push00 acc) := by
  rfl

noncomputable def fragment0198215Acc00100 : List SourceJson := fragment0198215Chunk000Push00 fragment0198215Acc00000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0198215_array_chunk_000"
  err.flush

noncomputable def fragment0198215Chunk001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0198215Chunk001Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '6']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '9']), .number (String.ofList ['3', '2']), .number (String.ofList ['3', '4'])]) :: ((.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['8']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '6']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '9']), .number (String.ofList ['3', '2']), .number (String.ofList ['3', '4'])]) :: (acc))

theorem array_fragment0198215_chunk_001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 21) (SourceJson.white (fragment0198215Chunk001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 19) (SourceJson.white tail) (fragment0198215Chunk001Push00 acc) := by
  rfl

noncomputable def fragment0198215Acc00200 : List SourceJson := fragment0198215Chunk001Push00 fragment0198215Acc00100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0198215_array_chunk_001"
  err.flush

noncomputable def fragment0198215Chunk002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0198215Chunk002Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '6']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '9']), .number (String.ofList ['3', '2']), .number (String.ofList ['3', '4'])]) :: ((.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '6']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4'])]) :: (acc))

theorem array_fragment0198215_chunk_002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 19) (SourceJson.white (fragment0198215Chunk002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 17) (SourceJson.white tail) (fragment0198215Chunk002Push00 acc) := by
  rfl

noncomputable def fragment0198215Acc00300 : List SourceJson := fragment0198215Chunk002Push00 fragment0198215Acc00200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0198215_array_chunk_002"
  err.flush

noncomputable def fragment0198215Chunk003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0198215Chunk003Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['5']), .number (String.ofList ['1', '3']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '9']), .number (String.ofList ['3', '4'])]) :: ((.arr [.number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '9']), .number (String.ofList ['3', '2']), .number (String.ofList ['3', '4'])]) :: (acc))

theorem array_fragment0198215_chunk_003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 17) (SourceJson.white (fragment0198215Chunk003Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 15) (SourceJson.white tail) (fragment0198215Chunk003Push00 acc) := by
  rfl

noncomputable def fragment0198215Acc00400 : List SourceJson := fragment0198215Chunk003Push00 fragment0198215Acc00300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0198215_array_chunk_003"
  err.flush

noncomputable def fragment0198215Chunk004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']']
noncomputable def fragment0198215Chunk004Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1', '6']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['3', '2'])]) :: (acc)

theorem array_fragment0198215_chunk_004 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 15) (SourceJson.white (fragment0198215Chunk004Chars00 ++ tail)) acc =
      .ok (.arr ((fragment0198215Chunk004Push00 acc).reverse), tail) := by
  rfl

noncomputable def fragment0198215Acc00500 : List SourceJson := fragment0198215Chunk004Push00 fragment0198215Acc00400

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0198215_array_chunk_004"
  err.flush

noncomputable def fragment0198215Chars : List Char := '[' :: (fragment0198215Chunk000Chars00 ++ fragment0198215Chunk001Chars00 ++ fragment0198215Chunk002Chars00 ++ fragment0198215Chunk003Chars00 ++ fragment0198215Chunk004Chars00)
noncomputable def fragment0198215Value : SourceJson := .arr (fragment0198215Acc00500.reverse)

theorem value_fragment0198215 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 24) (fragment0198215Chars ++ tail) =
      .ok (fragment0198215Value, tail) := by
  have hinput : fragment0198215Chars ++ tail = '[' :: (fragment0198215Chunk000Chars00 ++ (fragment0198215Chunk001Chars00 ++ (fragment0198215Chunk002Chars00 ++ (fragment0198215Chunk003Chars00 ++ (fragment0198215Chunk004Chars00 ++ (tail)))))) := by
    simp only [fragment0198215Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 24) (fragment0198215Chars ++ tail) =
        SourceJson.value (fuel + 24) ('[' :: (fragment0198215Chunk000Chars00 ++ (fragment0198215Chunk001Chars00 ++ (fragment0198215Chunk002Chars00 ++ (fragment0198215Chunk003Chars00 ++ (fragment0198215Chunk004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 24)) hinput
    _ = SourceJson.array (fuel + 23) (SourceJson.white (fragment0198215Chunk000Chars00 ++ (fragment0198215Chunk001Chars00 ++ (fragment0198215Chunk002Chars00 ++ (fragment0198215Chunk003Chars00 ++ (fragment0198215Chunk004Chars00 ++ (tail))))))) fragment0198215Acc00000 := by rfl
    _ = SourceJson.array (fuel + 21) (SourceJson.white (fragment0198215Chunk001Chars00 ++ (fragment0198215Chunk002Chars00 ++ (fragment0198215Chunk003Chars00 ++ (fragment0198215Chunk004Chars00 ++ (tail)))))) fragment0198215Acc00100 := array_fragment0198215_chunk_000 fuel (fragment0198215Chunk001Chars00 ++ (fragment0198215Chunk002Chars00 ++ (fragment0198215Chunk003Chars00 ++ (fragment0198215Chunk004Chars00 ++ (tail))))) fragment0198215Acc00000
    _ = SourceJson.array (fuel + 19) (SourceJson.white (fragment0198215Chunk002Chars00 ++ (fragment0198215Chunk003Chars00 ++ (fragment0198215Chunk004Chars00 ++ (tail))))) fragment0198215Acc00200 := array_fragment0198215_chunk_001 fuel (fragment0198215Chunk002Chars00 ++ (fragment0198215Chunk003Chars00 ++ (fragment0198215Chunk004Chars00 ++ (tail)))) fragment0198215Acc00100
    _ = SourceJson.array (fuel + 17) (SourceJson.white (fragment0198215Chunk003Chars00 ++ (fragment0198215Chunk004Chars00 ++ (tail)))) fragment0198215Acc00300 := array_fragment0198215_chunk_002 fuel (fragment0198215Chunk003Chars00 ++ (fragment0198215Chunk004Chars00 ++ (tail))) fragment0198215Acc00200
    _ = SourceJson.array (fuel + 15) (SourceJson.white (fragment0198215Chunk004Chars00 ++ (tail))) fragment0198215Acc00400 := array_fragment0198215_chunk_003 fuel (fragment0198215Chunk004Chars00 ++ (tail)) fragment0198215Acc00300
    _ = .ok (fragment0198215Value, tail) := array_fragment0198215_chunk_004 fuel (tail) fragment0198215Acc00400

noncomputable def fragment0197902Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0197902Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0197902Field000Value00 : SourceJson := .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '6']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '9']), .number (String.ofList ['3', '2']), .number (String.ofList ['3', '4'])]
noncomputable def fragment0197902Acc00100 : List (String × SourceJson) := (fragment0197902Field000Key00, fragment0197902Field000Value00) :: fragment0197902Acc00000
noncomputable def fragment0197902Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0197902_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 28) (SourceJson.white (fragment0197902Field000Chars00 ++ tail)) fragment0197902Acc00000 =
      SourceJson.object (fuel + 27) (SourceJson.white tail) fragment0197902Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0197902_object_field_000"
  err.flush

noncomputable def fragment0197902Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0197902Field001Value00 : SourceJson := .number (String.ofList ['6'])
noncomputable def fragment0197902Acc00200 : List (String × SourceJson) := (fragment0197902Field001Key00, fragment0197902Field001Value00) :: fragment0197902Acc00100
noncomputable def fragment0197902Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '6', ',']

theorem object_fragment0197902_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 27) (SourceJson.white (fragment0197902Field001Chars00 ++ tail)) fragment0197902Acc00100 =
      SourceJson.object (fuel + 26) (SourceJson.white tail) fragment0197902Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0197902_object_field_001"
  err.flush

noncomputable def fragment0197902Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0197902Field002Value00 : SourceJson := .number (String.ofList ['3', '4'])
noncomputable def fragment0197902Acc00300 : List (String × SourceJson) := (fragment0197902Field002Key00, fragment0197902Field002Value00) :: fragment0197902Acc00200
noncomputable def fragment0197902Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '3', '4', ',']

theorem object_fragment0197902_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 26) (SourceJson.white (fragment0197902Field002Chars00 ++ tail)) fragment0197902Acc00200 =
      SourceJson.object (fuel + 25) (SourceJson.white tail) fragment0197902Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0197902_object_field_002"
  err.flush

noncomputable def fragment0197902Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0197902Field003Value00 : SourceJson := fragment0198215Value
noncomputable def fragment0197902Acc00400 : List (String × SourceJson) := (fragment0197902Field003Key00, fragment0197902Field003Value00) :: fragment0197902Acc00300
noncomputable def fragment0197902Field003HeaderChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ']
noncomputable def fragment0197902Field003SuffixChars00 : List Char := [',']
noncomputable def fragment0197902Field003Chars00 : List Char := fragment0197902Field003HeaderChars00 ++ fragment0198215Chars ++ fragment0197902Field003SuffixChars00

noncomputable def fragment0197902Field003AfterValue00 (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending => .ok (.obj (((fragment0197902Field003Key00, result.1) :: fragment0197902Acc00300).reverse), ending)
  | ',' :: ending => SourceJson.object fuel (SourceJson.white ending) ((fragment0197902Field003Key00, result.1) :: fragment0197902Acc00300)
  | _ => .error "object separator missing"

theorem object_fragment0197902_field_003_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 25) (SourceJson.white (fragment0197902Field003HeaderChars00 ++ rest)) fragment0197902Acc00300 =
      (SourceJson.value (fuel + 24) rest).bind (fragment0197902Field003AfterValue00 (fuel + 24)) := by rfl

theorem object_fragment0197902_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 25) (SourceJson.white (fragment0197902Field003Chars00 ++ tail)) fragment0197902Acc00300 =
      SourceJson.object (fuel + 24) (SourceJson.white tail) fragment0197902Acc00400 := by
  have hinput : fragment0197902Field003Chars00 ++ tail = fragment0197902Field003HeaderChars00 ++ (fragment0198215Chars ++ (fragment0197902Field003SuffixChars00 ++ tail)) := by
    simp only [fragment0197902Field003Chars00, List.append_assoc]
  calc
    SourceJson.object (fuel + 25) (SourceJson.white (fragment0197902Field003Chars00 ++ tail)) fragment0197902Acc00300 =
        SourceJson.object (fuel + 25)
          (SourceJson.white (fragment0197902Field003HeaderChars00 ++ (fragment0198215Chars ++ (fragment0197902Field003SuffixChars00 ++ tail)))) fragment0197902Acc00300 :=
      congrArg (fun s => SourceJson.object (fuel + 25) (SourceJson.white s) fragment0197902Acc00300) hinput
    _ = (SourceJson.value (fuel + 24) (fragment0198215Chars ++ (fragment0197902Field003SuffixChars00 ++ tail))).bind
        (fragment0197902Field003AfterValue00 (fuel + 24)) := object_fragment0197902_field_003_header fuel (fragment0198215Chars ++ (fragment0197902Field003SuffixChars00 ++ tail))
    _ = (Except.ok (fragment0198215Value, fragment0197902Field003SuffixChars00 ++ tail)).bind (fragment0197902Field003AfterValue00 (fuel + 24)) :=
      congrArg (fun result => result.bind (fragment0197902Field003AfterValue00 (fuel + 24)))
        (value_fragment0198215 (fuel + 0) (fragment0197902Field003SuffixChars00 ++ tail))
    _ = SourceJson.object (fuel + 24) (SourceJson.white tail) fragment0197902Acc00400 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0197902_object_field_003"
  err.flush

noncomputable def fragment0197902Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0197902Field004Value00 : SourceJson := .number (String.ofList ['1', '1'])
noncomputable def fragment0197902Acc00500 : List (String × SourceJson) := (fragment0197902Field004Key00, fragment0197902Field004Value00) :: fragment0197902Acc00400
noncomputable def fragment0197902Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0197902_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 24) (SourceJson.white (fragment0197902Field004Chars00 ++ tail)) fragment0197902Acc00400 =
      .ok (.obj (fragment0197902Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0197902_object_field_004"
  err.flush

noncomputable def fragment0197902Chars : List Char := '{' :: (fragment0197902Field000Chars00 ++ fragment0197902Field001Chars00 ++ fragment0197902Field002Chars00 ++ fragment0197902Field003Chars00 ++ fragment0197902Field004Chars00)
noncomputable def fragment0197902Value : SourceJson := .obj (fragment0197902Acc00500.reverse)

theorem value_fragment0197902 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 29) (fragment0197902Chars ++ tail) =
      .ok (fragment0197902Value, tail) := by
  have hinput : fragment0197902Chars ++ tail = '{' :: (fragment0197902Field000Chars00 ++ (fragment0197902Field001Chars00 ++ (fragment0197902Field002Chars00 ++ (fragment0197902Field003Chars00 ++ (fragment0197902Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0197902Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 29) (fragment0197902Chars ++ tail) =
        SourceJson.value (fuel + 29) ('{' :: (fragment0197902Field000Chars00 ++ (fragment0197902Field001Chars00 ++ (fragment0197902Field002Chars00 ++ (fragment0197902Field003Chars00 ++ (fragment0197902Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 29)) hinput
    _ = SourceJson.object (fuel + 28) (SourceJson.white (fragment0197902Field000Chars00 ++ (fragment0197902Field001Chars00 ++ (fragment0197902Field002Chars00 ++ (fragment0197902Field003Chars00 ++ (fragment0197902Field004Chars00 ++ (tail))))))) fragment0197902Acc00000 := by rfl
    _ = SourceJson.object (fuel + 27) (SourceJson.white (fragment0197902Field001Chars00 ++ (fragment0197902Field002Chars00 ++ (fragment0197902Field003Chars00 ++ (fragment0197902Field004Chars00 ++ (tail)))))) fragment0197902Acc00100 := object_fragment0197902_field_000 fuel (fragment0197902Field001Chars00 ++ (fragment0197902Field002Chars00 ++ (fragment0197902Field003Chars00 ++ (fragment0197902Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 26) (SourceJson.white (fragment0197902Field002Chars00 ++ (fragment0197902Field003Chars00 ++ (fragment0197902Field004Chars00 ++ (tail))))) fragment0197902Acc00200 := object_fragment0197902_field_001 fuel (fragment0197902Field002Chars00 ++ (fragment0197902Field003Chars00 ++ (fragment0197902Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 25) (SourceJson.white (fragment0197902Field003Chars00 ++ (fragment0197902Field004Chars00 ++ (tail)))) fragment0197902Acc00300 := object_fragment0197902_field_002 fuel (fragment0197902Field003Chars00 ++ (fragment0197902Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 24) (SourceJson.white (fragment0197902Field004Chars00 ++ (tail))) fragment0197902Acc00400 := object_fragment0197902_field_003 fuel (fragment0197902Field004Chars00 ++ (tail))
    _ = .ok (fragment0197902Value, tail) := object_fragment0197902_field_004 fuel (tail)

noncomputable def fragment0200188Acc00000 : List SourceJson := []

noncomputable def fragment0200188Chunk000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0200188Chunk000Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['8']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '3']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '9'])]) :: ((.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '3']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '8'])]) :: (acc))

theorem array_fragment0200188_chunk_000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 16) (SourceJson.white (fragment0200188Chunk000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 14) (SourceJson.white tail) (fragment0200188Chunk000Push00 acc) := by
  rfl

noncomputable def fragment0200188Acc00100 : List SourceJson := fragment0200188Chunk000Push00 fragment0200188Acc00000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0200188_array_chunk_000"
  err.flush

noncomputable def fragment0200188Chunk001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0200188Chunk001Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1'])]) :: ((.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '3']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '9'])]) :: (acc))

theorem array_fragment0200188_chunk_001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 14) (SourceJson.white (fragment0200188Chunk001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 12) (SourceJson.white tail) (fragment0200188Chunk001Push00 acc) := by
  rfl

noncomputable def fragment0200188Acc00200 : List SourceJson := fragment0200188Chunk001Push00 fragment0200188Acc00100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0200188_array_chunk_001"
  err.flush

noncomputable def fragment0200188Chunk002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0200188Chunk002Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '9'])]) :: ((.arr [.number (String.ofList ['1']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '3']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '9'])]) :: (acc))

theorem array_fragment0200188_chunk_002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 12) (SourceJson.white (fragment0200188Chunk002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 10) (SourceJson.white tail) (fragment0200188Chunk002Push00 acc) := by
  rfl

noncomputable def fragment0200188Acc00300 : List SourceJson := fragment0200188Chunk002Push00 fragment0200188Acc00200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0200188_array_chunk_002"
  err.flush

noncomputable def fragment0200188Chunk003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']']
noncomputable def fragment0200188Chunk003Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['5']), .number (String.ofList ['1', '3']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '9'])]) :: (acc)

theorem array_fragment0200188_chunk_003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 10) (SourceJson.white (fragment0200188Chunk003Chars00 ++ tail)) acc =
      .ok (.arr ((fragment0200188Chunk003Push00 acc).reverse), tail) := by
  rfl

noncomputable def fragment0200188Acc00400 : List SourceJson := fragment0200188Chunk003Push00 fragment0200188Acc00300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0200188_array_chunk_003"
  err.flush

noncomputable def fragment0200188Chars : List Char := '[' :: (fragment0200188Chunk000Chars00 ++ fragment0200188Chunk001Chars00 ++ fragment0200188Chunk002Chars00 ++ fragment0200188Chunk003Chars00)
noncomputable def fragment0200188Value : SourceJson := .arr (fragment0200188Acc00400.reverse)

theorem value_fragment0200188 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 17) (fragment0200188Chars ++ tail) =
      .ok (fragment0200188Value, tail) := by
  have hinput : fragment0200188Chars ++ tail = '[' :: (fragment0200188Chunk000Chars00 ++ (fragment0200188Chunk001Chars00 ++ (fragment0200188Chunk002Chars00 ++ (fragment0200188Chunk003Chars00 ++ (tail))))) := by
    simp only [fragment0200188Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 17) (fragment0200188Chars ++ tail) =
        SourceJson.value (fuel + 17) ('[' :: (fragment0200188Chunk000Chars00 ++ (fragment0200188Chunk001Chars00 ++ (fragment0200188Chunk002Chars00 ++ (fragment0200188Chunk003Chars00 ++ (tail)))))) :=
      congrArg (SourceJson.value (fuel + 17)) hinput
    _ = SourceJson.array (fuel + 16) (SourceJson.white (fragment0200188Chunk000Chars00 ++ (fragment0200188Chunk001Chars00 ++ (fragment0200188Chunk002Chars00 ++ (fragment0200188Chunk003Chars00 ++ (tail)))))) fragment0200188Acc00000 := by rfl
    _ = SourceJson.array (fuel + 14) (SourceJson.white (fragment0200188Chunk001Chars00 ++ (fragment0200188Chunk002Chars00 ++ (fragment0200188Chunk003Chars00 ++ (tail))))) fragment0200188Acc00100 := array_fragment0200188_chunk_000 fuel (fragment0200188Chunk001Chars00 ++ (fragment0200188Chunk002Chars00 ++ (fragment0200188Chunk003Chars00 ++ (tail)))) fragment0200188Acc00000
    _ = SourceJson.array (fuel + 12) (SourceJson.white (fragment0200188Chunk002Chars00 ++ (fragment0200188Chunk003Chars00 ++ (tail)))) fragment0200188Acc00200 := array_fragment0200188_chunk_001 fuel (fragment0200188Chunk002Chars00 ++ (fragment0200188Chunk003Chars00 ++ (tail))) fragment0200188Acc00100
    _ = SourceJson.array (fuel + 10) (SourceJson.white (fragment0200188Chunk003Chars00 ++ (tail))) fragment0200188Acc00300 := array_fragment0200188_chunk_002 fuel (fragment0200188Chunk003Chars00 ++ (tail)) fragment0200188Acc00200
    _ = .ok (fragment0200188Value, tail) := array_fragment0200188_chunk_003 fuel (tail) fragment0200188Acc00300

noncomputable def fragment0199966Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0199966Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0199966Field000Value00 : SourceJson := .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '3']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '9'])]
noncomputable def fragment0199966Acc00100 : List (String × SourceJson) := (fragment0199966Field000Key00, fragment0199966Field000Value00) :: fragment0199966Acc00000
noncomputable def fragment0199966Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0199966_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 21) (SourceJson.white (fragment0199966Field000Chars00 ++ tail)) fragment0199966Acc00000 =
      SourceJson.object (fuel + 20) (SourceJson.white tail) fragment0199966Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0199966_object_field_000"
  err.flush

noncomputable def fragment0199966Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0199966Field001Value00 : SourceJson := .number (String.ofList ['5'])
noncomputable def fragment0199966Acc00200 : List (String × SourceJson) := (fragment0199966Field001Key00, fragment0199966Field001Value00) :: fragment0199966Acc00100
noncomputable def fragment0199966Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '5', ',']

theorem object_fragment0199966_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 20) (SourceJson.white (fragment0199966Field001Chars00 ++ tail)) fragment0199966Acc00100 =
      SourceJson.object (fuel + 19) (SourceJson.white tail) fragment0199966Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0199966_object_field_001"
  err.flush

noncomputable def fragment0199966Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0199966Field002Value00 : SourceJson := .number (String.ofList ['2', '9'])
noncomputable def fragment0199966Acc00300 : List (String × SourceJson) := (fragment0199966Field002Key00, fragment0199966Field002Value00) :: fragment0199966Acc00200
noncomputable def fragment0199966Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '2', '9', ',']

theorem object_fragment0199966_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 19) (SourceJson.white (fragment0199966Field002Chars00 ++ tail)) fragment0199966Acc00200 =
      SourceJson.object (fuel + 18) (SourceJson.white tail) fragment0199966Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0199966_object_field_002"
  err.flush

noncomputable def fragment0199966Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0199966Field003Value00 : SourceJson := fragment0200188Value
noncomputable def fragment0199966Acc00400 : List (String × SourceJson) := (fragment0199966Field003Key00, fragment0199966Field003Value00) :: fragment0199966Acc00300
noncomputable def fragment0199966Field003HeaderChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ']
noncomputable def fragment0199966Field003SuffixChars00 : List Char := [',']
noncomputable def fragment0199966Field003Chars00 : List Char := fragment0199966Field003HeaderChars00 ++ fragment0200188Chars ++ fragment0199966Field003SuffixChars00

noncomputable def fragment0199966Field003AfterValue00 (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending => .ok (.obj (((fragment0199966Field003Key00, result.1) :: fragment0199966Acc00300).reverse), ending)
  | ',' :: ending => SourceJson.object fuel (SourceJson.white ending) ((fragment0199966Field003Key00, result.1) :: fragment0199966Acc00300)
  | _ => .error "object separator missing"

theorem object_fragment0199966_field_003_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 18) (SourceJson.white (fragment0199966Field003HeaderChars00 ++ rest)) fragment0199966Acc00300 =
      (SourceJson.value (fuel + 17) rest).bind (fragment0199966Field003AfterValue00 (fuel + 17)) := by rfl

theorem object_fragment0199966_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 18) (SourceJson.white (fragment0199966Field003Chars00 ++ tail)) fragment0199966Acc00300 =
      SourceJson.object (fuel + 17) (SourceJson.white tail) fragment0199966Acc00400 := by
  have hinput : fragment0199966Field003Chars00 ++ tail = fragment0199966Field003HeaderChars00 ++ (fragment0200188Chars ++ (fragment0199966Field003SuffixChars00 ++ tail)) := by
    simp only [fragment0199966Field003Chars00, List.append_assoc]
  calc
    SourceJson.object (fuel + 18) (SourceJson.white (fragment0199966Field003Chars00 ++ tail)) fragment0199966Acc00300 =
        SourceJson.object (fuel + 18)
          (SourceJson.white (fragment0199966Field003HeaderChars00 ++ (fragment0200188Chars ++ (fragment0199966Field003SuffixChars00 ++ tail)))) fragment0199966Acc00300 :=
      congrArg (fun s => SourceJson.object (fuel + 18) (SourceJson.white s) fragment0199966Acc00300) hinput
    _ = (SourceJson.value (fuel + 17) (fragment0200188Chars ++ (fragment0199966Field003SuffixChars00 ++ tail))).bind
        (fragment0199966Field003AfterValue00 (fuel + 17)) := object_fragment0199966_field_003_header fuel (fragment0200188Chars ++ (fragment0199966Field003SuffixChars00 ++ tail))
    _ = (Except.ok (fragment0200188Value, fragment0199966Field003SuffixChars00 ++ tail)).bind (fragment0199966Field003AfterValue00 (fuel + 17)) :=
      congrArg (fun result => result.bind (fragment0199966Field003AfterValue00 (fuel + 17)))
        (value_fragment0200188 (fuel + 0) (fragment0199966Field003SuffixChars00 ++ tail))
    _ = SourceJson.object (fuel + 17) (SourceJson.white tail) fragment0199966Acc00400 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0199966_object_field_003"
  err.flush

noncomputable def fragment0199966Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0199966Field004Value00 : SourceJson := .number (String.ofList ['5'])
noncomputable def fragment0199966Acc00500 : List (String × SourceJson) := (fragment0199966Field004Key00, fragment0199966Field004Value00) :: fragment0199966Acc00400
noncomputable def fragment0199966Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '5', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0199966_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 17) (SourceJson.white (fragment0199966Field004Chars00 ++ tail)) fragment0199966Acc00400 =
      .ok (.obj (fragment0199966Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0199966_object_field_004"
  err.flush

noncomputable def fragment0199966Chars : List Char := '{' :: (fragment0199966Field000Chars00 ++ fragment0199966Field001Chars00 ++ fragment0199966Field002Chars00 ++ fragment0199966Field003Chars00 ++ fragment0199966Field004Chars00)
noncomputable def fragment0199966Value : SourceJson := .obj (fragment0199966Acc00500.reverse)

theorem value_fragment0199966 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 22) (fragment0199966Chars ++ tail) =
      .ok (fragment0199966Value, tail) := by
  have hinput : fragment0199966Chars ++ tail = '{' :: (fragment0199966Field000Chars00 ++ (fragment0199966Field001Chars00 ++ (fragment0199966Field002Chars00 ++ (fragment0199966Field003Chars00 ++ (fragment0199966Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0199966Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 22) (fragment0199966Chars ++ tail) =
        SourceJson.value (fuel + 22) ('{' :: (fragment0199966Field000Chars00 ++ (fragment0199966Field001Chars00 ++ (fragment0199966Field002Chars00 ++ (fragment0199966Field003Chars00 ++ (fragment0199966Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 22)) hinput
    _ = SourceJson.object (fuel + 21) (SourceJson.white (fragment0199966Field000Chars00 ++ (fragment0199966Field001Chars00 ++ (fragment0199966Field002Chars00 ++ (fragment0199966Field003Chars00 ++ (fragment0199966Field004Chars00 ++ (tail))))))) fragment0199966Acc00000 := by rfl
    _ = SourceJson.object (fuel + 20) (SourceJson.white (fragment0199966Field001Chars00 ++ (fragment0199966Field002Chars00 ++ (fragment0199966Field003Chars00 ++ (fragment0199966Field004Chars00 ++ (tail)))))) fragment0199966Acc00100 := object_fragment0199966_field_000 fuel (fragment0199966Field001Chars00 ++ (fragment0199966Field002Chars00 ++ (fragment0199966Field003Chars00 ++ (fragment0199966Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 19) (SourceJson.white (fragment0199966Field002Chars00 ++ (fragment0199966Field003Chars00 ++ (fragment0199966Field004Chars00 ++ (tail))))) fragment0199966Acc00200 := object_fragment0199966_field_001 fuel (fragment0199966Field002Chars00 ++ (fragment0199966Field003Chars00 ++ (fragment0199966Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 18) (SourceJson.white (fragment0199966Field003Chars00 ++ (fragment0199966Field004Chars00 ++ (tail)))) fragment0199966Acc00300 := object_fragment0199966_field_002 fuel (fragment0199966Field003Chars00 ++ (fragment0199966Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 17) (SourceJson.white (fragment0199966Field004Chars00 ++ (tail))) fragment0199966Acc00400 := object_fragment0199966_field_003 fuel (fragment0199966Field004Chars00 ++ (tail))
    _ = .ok (fragment0199966Value, tail) := object_fragment0199966_field_004 fuel (tail)

noncomputable def fragment0201118Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0201118Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0201118Field000Value00 : SourceJson := .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '3']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '8'])]
noncomputable def fragment0201118Acc00100 : List (String × SourceJson) := (fragment0201118Field000Key00, fragment0201118Field000Value00) :: fragment0201118Acc00000
noncomputable def fragment0201118Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0201118_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 18) (SourceJson.white (fragment0201118Field000Chars00 ++ tail)) fragment0201118Acc00000 =
      SourceJson.object (fuel + 17) (SourceJson.white tail) fragment0201118Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0201118_object_field_000"
  err.flush

noncomputable def fragment0201118Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0201118Field001Value00 : SourceJson := .number (String.ofList ['4'])
noncomputable def fragment0201118Acc00200 : List (String × SourceJson) := (fragment0201118Field001Key00, fragment0201118Field001Value00) :: fragment0201118Acc00100
noncomputable def fragment0201118Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '4', ',']

theorem object_fragment0201118_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 17) (SourceJson.white (fragment0201118Field001Chars00 ++ tail)) fragment0201118Acc00100 =
      SourceJson.object (fuel + 16) (SourceJson.white tail) fragment0201118Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0201118_object_field_001"
  err.flush

noncomputable def fragment0201118Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0201118Field002Value00 : SourceJson := .number (String.ofList ['2', '8'])
noncomputable def fragment0201118Acc00300 : List (String × SourceJson) := (fragment0201118Field002Key00, fragment0201118Field002Value00) :: fragment0201118Acc00200
noncomputable def fragment0201118Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '2', '8', ',']

theorem object_fragment0201118_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 16) (SourceJson.white (fragment0201118Field002Chars00 ++ tail)) fragment0201118Acc00200 =
      SourceJson.object (fuel + 15) (SourceJson.white tail) fragment0201118Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0201118_object_field_002"
  err.flush

noncomputable def fragment0201118Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0201118Field003Value00 : SourceJson := .arr [.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['8']), .number (String.ofList ['1', '3']), .number (String.ofList ['2', '5'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '3']), .number (String.ofList ['2', '8'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['8']), .number (String.ofList ['1', '0'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '3']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '8'])], .arr [.number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '8'])], .arr [.number (String.ofList ['5']), .number (String.ofList ['1', '3']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '8'])]]
noncomputable def fragment0201118Acc00400 : List (String × SourceJson) := (fragment0201118Field003Key00, fragment0201118Field003Value00) :: fragment0201118Acc00300
noncomputable def fragment0201118Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0201118_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 15) (SourceJson.white (fragment0201118Field003Chars00 ++ tail)) fragment0201118Acc00300 =
      SourceJson.object (fuel + 14) (SourceJson.white tail) fragment0201118Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0201118_object_field_003"
  err.flush

noncomputable def fragment0201118Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0201118Field004Value00 : SourceJson := .number (String.ofList ['4'])
noncomputable def fragment0201118Acc00500 : List (String × SourceJson) := (fragment0201118Field004Key00, fragment0201118Field004Value00) :: fragment0201118Acc00400
noncomputable def fragment0201118Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0201118_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 14) (SourceJson.white (fragment0201118Field004Chars00 ++ tail)) fragment0201118Acc00400 =
      .ok (.obj (fragment0201118Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0201118_object_field_004"
  err.flush

noncomputable def fragment0201118Chars : List Char := '{' :: (fragment0201118Field000Chars00 ++ fragment0201118Field001Chars00 ++ fragment0201118Field002Chars00 ++ fragment0201118Field003Chars00 ++ fragment0201118Field004Chars00)
noncomputable def fragment0201118Value : SourceJson := .obj (fragment0201118Acc00500.reverse)

theorem value_fragment0201118 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 19) (fragment0201118Chars ++ tail) =
      .ok (fragment0201118Value, tail) := by
  have hinput : fragment0201118Chars ++ tail = '{' :: (fragment0201118Field000Chars00 ++ (fragment0201118Field001Chars00 ++ (fragment0201118Field002Chars00 ++ (fragment0201118Field003Chars00 ++ (fragment0201118Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0201118Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 19) (fragment0201118Chars ++ tail) =
        SourceJson.value (fuel + 19) ('{' :: (fragment0201118Field000Chars00 ++ (fragment0201118Field001Chars00 ++ (fragment0201118Field002Chars00 ++ (fragment0201118Field003Chars00 ++ (fragment0201118Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 19)) hinput
    _ = SourceJson.object (fuel + 18) (SourceJson.white (fragment0201118Field000Chars00 ++ (fragment0201118Field001Chars00 ++ (fragment0201118Field002Chars00 ++ (fragment0201118Field003Chars00 ++ (fragment0201118Field004Chars00 ++ (tail))))))) fragment0201118Acc00000 := by rfl
    _ = SourceJson.object (fuel + 17) (SourceJson.white (fragment0201118Field001Chars00 ++ (fragment0201118Field002Chars00 ++ (fragment0201118Field003Chars00 ++ (fragment0201118Field004Chars00 ++ (tail)))))) fragment0201118Acc00100 := object_fragment0201118_field_000 fuel (fragment0201118Field001Chars00 ++ (fragment0201118Field002Chars00 ++ (fragment0201118Field003Chars00 ++ (fragment0201118Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 16) (SourceJson.white (fragment0201118Field002Chars00 ++ (fragment0201118Field003Chars00 ++ (fragment0201118Field004Chars00 ++ (tail))))) fragment0201118Acc00200 := object_fragment0201118_field_001 fuel (fragment0201118Field002Chars00 ++ (fragment0201118Field003Chars00 ++ (fragment0201118Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 15) (SourceJson.white (fragment0201118Field003Chars00 ++ (fragment0201118Field004Chars00 ++ (tail)))) fragment0201118Acc00300 := object_fragment0201118_field_002 fuel (fragment0201118Field003Chars00 ++ (fragment0201118Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 14) (SourceJson.white (fragment0201118Field004Chars00 ++ (tail))) fragment0201118Acc00400 := object_fragment0201118_field_003 fuel (fragment0201118Field004Chars00 ++ (tail))
    _ = .ok (fragment0201118Value, tail) := object_fragment0201118_field_004 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0032_before_reader"
  err.flush

noncomputable def chunk0032LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0032SuffixChars00 : List Char := [',']
noncomputable def chunk0032Chars00 : List Char := chunk0032LeadChars00 ++ fragment0197902Chars ++ chunk0032SuffixChars00
noncomputable def chunk0032Push00 (acc : List SourceJson) : List SourceJson := fragment0197902Value :: acc

noncomputable def chunk0032AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0032_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 61)
      (SourceJson.white (chunk0032LeadChars00 ++ (fragment0197902Chars ++ rest))) acc =
      (SourceJson.value (fuel + 60) (fragment0197902Chars ++ rest)).bind
        (chunk0032AfterValue00 (fuel + 60) acc) := by rfl

theorem array_chunk0032 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 61) (SourceJson.white (chunk0032Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 60) (SourceJson.white tail) (chunk0032Push00 acc) := by
  have hinput : chunk0032Chars00 ++ tail = chunk0032LeadChars00 ++ (fragment0197902Chars ++ (chunk0032SuffixChars00 ++ tail)) := by
    simp only [chunk0032Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 61) (SourceJson.white (chunk0032Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 61)
          (SourceJson.white (chunk0032LeadChars00 ++ (fragment0197902Chars ++ (chunk0032SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 61) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 60) (fragment0197902Chars ++ (chunk0032SuffixChars00 ++ tail))).bind
        (chunk0032AfterValue00 (fuel + 60) acc) := array_chunk0032_head fuel (chunk0032SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0197902Value, chunk0032SuffixChars00 ++ tail)).bind
        (chunk0032AfterValue00 (fuel + 60) acc) :=
      congrArg (fun result => result.bind (chunk0032AfterValue00 (fuel + 60) acc))
        (value_fragment0197902 (fuel + 31) (chunk0032SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 60) (SourceJson.white tail) (chunk0032Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0032_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0033_before_reader"
  err.flush

noncomputable def chunk0033LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0033SuffixChars00 : List Char := [',']
noncomputable def chunk0033Chars00 : List Char := chunk0033LeadChars00 ++ fragment0199966Chars ++ chunk0033SuffixChars00
noncomputable def chunk0033Push00 (acc : List SourceJson) : List SourceJson := fragment0199966Value :: acc

noncomputable def chunk0033AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0033_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 60)
      (SourceJson.white (chunk0033LeadChars00 ++ (fragment0199966Chars ++ rest))) acc =
      (SourceJson.value (fuel + 59) (fragment0199966Chars ++ rest)).bind
        (chunk0033AfterValue00 (fuel + 59) acc) := by rfl

theorem array_chunk0033 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 60) (SourceJson.white (chunk0033Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 59) (SourceJson.white tail) (chunk0033Push00 acc) := by
  have hinput : chunk0033Chars00 ++ tail = chunk0033LeadChars00 ++ (fragment0199966Chars ++ (chunk0033SuffixChars00 ++ tail)) := by
    simp only [chunk0033Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 60) (SourceJson.white (chunk0033Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 60)
          (SourceJson.white (chunk0033LeadChars00 ++ (fragment0199966Chars ++ (chunk0033SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 60) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 59) (fragment0199966Chars ++ (chunk0033SuffixChars00 ++ tail))).bind
        (chunk0033AfterValue00 (fuel + 59) acc) := array_chunk0033_head fuel (chunk0033SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0199966Value, chunk0033SuffixChars00 ++ tail)).bind
        (chunk0033AfterValue00 (fuel + 59) acc) :=
      congrArg (fun result => result.bind (chunk0033AfterValue00 (fuel + 59) acc))
        (value_fragment0199966 (fuel + 37) (chunk0033SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 59) (SourceJson.white tail) (chunk0033Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0033_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0034_before_reader"
  err.flush

noncomputable def chunk0034LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0034SuffixChars00 : List Char := [',']
noncomputable def chunk0034Chars00 : List Char := chunk0034LeadChars00 ++ fragment0201118Chars ++ chunk0034SuffixChars00
noncomputable def chunk0034Push00 (acc : List SourceJson) : List SourceJson := fragment0201118Value :: acc

noncomputable def chunk0034AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0034_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 59)
      (SourceJson.white (chunk0034LeadChars00 ++ (fragment0201118Chars ++ rest))) acc =
      (SourceJson.value (fuel + 58) (fragment0201118Chars ++ rest)).bind
        (chunk0034AfterValue00 (fuel + 58) acc) := by rfl

theorem array_chunk0034 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 59) (SourceJson.white (chunk0034Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 58) (SourceJson.white tail) (chunk0034Push00 acc) := by
  have hinput : chunk0034Chars00 ++ tail = chunk0034LeadChars00 ++ (fragment0201118Chars ++ (chunk0034SuffixChars00 ++ tail)) := by
    simp only [chunk0034Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 59) (SourceJson.white (chunk0034Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 59)
          (SourceJson.white (chunk0034LeadChars00 ++ (fragment0201118Chars ++ (chunk0034SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 59) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 58) (fragment0201118Chars ++ (chunk0034SuffixChars00 ++ tail))).bind
        (chunk0034AfterValue00 (fuel + 58) acc) := array_chunk0034_head fuel (chunk0034SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0201118Value, chunk0034SuffixChars00 ++ tail)).bind
        (chunk0034AfterValue00 (fuel + 58) acc) :=
      congrArg (fun result => result.bind (chunk0034AfterValue00 (fuel + 58) acc))
        (value_fragment0201118 (fuel + 39) (chunk0034SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 58) (SourceJson.white tail) (chunk0034Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0034_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0032Chars00 ++ chunk0033Chars00 ++ chunk0034Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0034Push00 (chunk0033Push00 (chunk0032Push00 (acc)))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 61) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 58) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0032Chars00 ++ (chunk0033Chars00 ++ (chunk0034Chars00 ++ (tail))) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 61) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 61) (SourceJson.white (chunk0032Chars00 ++ (chunk0033Chars00 ++ (chunk0034Chars00 ++ (tail))))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 61) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 60) (SourceJson.white (chunk0033Chars00 ++ (chunk0034Chars00 ++ (tail)))) (chunk0032Push00 (acc)) := array_chunk0032 fuel (chunk0033Chars00 ++ (chunk0034Chars00 ++ (tail))) (acc)
    _ = SourceJson.array (fuel + 59) (SourceJson.white (chunk0034Chars00 ++ (tail))) (chunk0033Push00 (chunk0032Push00 (acc))) := array_chunk0033 fuel (chunk0034Chars00 ++ (tail)) (chunk0032Push00 (acc))
    _ = SourceJson.array (fuel + 58) (SourceJson.white tail) (blockPush acc) := array_chunk0034 fuel (tail) (chunk0033Push00 (chunk0032Push00 (acc)))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 197896).take 4054 = blockChars := by rfl

theorem block_original_split : sourceRest 197896 = blockChars ++ sourceRest 201950 := by
  calc
    sourceRest 197896 = (sourceRest 197896).take 4054 ++ (sourceRest 197896).drop 4054 :=
      (List.take_append_drop 4054 (sourceRest 197896)).symm
    _ = blockChars ++ (sourceRest 197896).drop 4054 :=
      congrArg (fun part => part ++ (sourceRest 197896).drop 4054) block_original_prefix
    _ = blockChars ++ sourceRest 201950 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 197896 4054)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 61) (SourceJson.white (sourceRest 197896)) acc =
      SourceJson.array (fuel + 58) (SourceJson.white (sourceRest 201950)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 61) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 201950) acc)

#print axioms array_fragment0198215_chunk_000
#print axioms array_fragment0198215_chunk_001
#print axioms array_fragment0198215_chunk_002
#print axioms array_fragment0198215_chunk_003
#print axioms array_fragment0198215_chunk_004
#print axioms value_fragment0198215
#print axioms object_fragment0197902_field_000
#print axioms object_fragment0197902_field_001
#print axioms object_fragment0197902_field_002
#print axioms object_fragment0197902_field_003_header
#print axioms object_fragment0197902_field_003
#print axioms object_fragment0197902_field_004
#print axioms value_fragment0197902
#print axioms array_fragment0200188_chunk_000
#print axioms array_fragment0200188_chunk_001
#print axioms array_fragment0200188_chunk_002
#print axioms array_fragment0200188_chunk_003
#print axioms value_fragment0200188
#print axioms object_fragment0199966_field_000
#print axioms object_fragment0199966_field_001
#print axioms object_fragment0199966_field_002
#print axioms object_fragment0199966_field_003_header
#print axioms object_fragment0199966_field_003
#print axioms object_fragment0199966_field_004
#print axioms value_fragment0199966
#print axioms object_fragment0201118_field_000
#print axioms object_fragment0201118_field_001
#print axioms object_fragment0201118_field_002
#print axioms object_fragment0201118_field_003
#print axioms object_fragment0201118_field_004
#print axioms value_fragment0201118
#print axioms array_chunk0032_head
#print axioms array_chunk0032
#print axioms array_chunk0033_head
#print axioms array_chunk0033
#print axioms array_chunk0034_head
#print axioms array_chunk0034
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end FaceLedgerBlock012

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
