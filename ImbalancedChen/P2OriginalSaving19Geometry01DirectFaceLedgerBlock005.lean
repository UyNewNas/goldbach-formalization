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

namespace FaceLedgerBlock005

noncomputable def fragment0174563Acc00000 : List SourceJson := []

noncomputable def fragment0174563Chunk000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0174563Chunk000Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1'])]) :: (acc))

theorem array_fragment0174563_chunk_000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 26) (SourceJson.white (fragment0174563Chunk000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 24) (SourceJson.white tail) (fragment0174563Chunk000Push00 acc) := by
  rfl

noncomputable def fragment0174563Acc00100 : List SourceJson := fragment0174563Chunk000Push00 fragment0174563Acc00000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0174563_array_chunk_000"
  err.flush

noncomputable def fragment0174563Chunk001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0174563Chunk001Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['7']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['6']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '4'])]) :: (acc))

theorem array_fragment0174563_chunk_001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 24) (SourceJson.white (fragment0174563Chunk001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 22) (SourceJson.white tail) (fragment0174563Chunk001Push00 acc) := by
  rfl

noncomputable def fragment0174563Acc00200 : List SourceJson := fragment0174563Chunk001Push00 fragment0174563Acc00100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0174563_array_chunk_001"
  err.flush

noncomputable def fragment0174563Chunk002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0174563Chunk002Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['9']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '2'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '8']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4'])]) :: (acc))

theorem array_fragment0174563_chunk_002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 22) (SourceJson.white (fragment0174563Chunk002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 20) (SourceJson.white tail) (fragment0174563Chunk002Push00 acc) := by
  rfl

noncomputable def fragment0174563Acc00300 : List SourceJson := fragment0174563Chunk002Push00 fragment0174563Acc00200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0174563_array_chunk_002"
  err.flush

noncomputable def fragment0174563Chunk003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0174563Chunk003Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4'])]) :: ((.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '6']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4'])]) :: (acc))

theorem array_fragment0174563_chunk_003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 20) (SourceJson.white (fragment0174563Chunk003Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 18) (SourceJson.white tail) (fragment0174563Chunk003Push00 acc) := by
  rfl

noncomputable def fragment0174563Acc00400 : List SourceJson := fragment0174563Chunk003Push00 fragment0174563Acc00300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0174563_array_chunk_003"
  err.flush

noncomputable def fragment0174563Chunk004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']']
noncomputable def fragment0174563Chunk004Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4'])]) :: (acc)

theorem array_fragment0174563_chunk_004 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 18) (SourceJson.white (fragment0174563Chunk004Chars00 ++ tail)) acc =
      .ok (.arr ((fragment0174563Chunk004Push00 acc).reverse), tail) := by
  rfl

noncomputable def fragment0174563Acc00500 : List SourceJson := fragment0174563Chunk004Push00 fragment0174563Acc00400

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0174563_array_chunk_004"
  err.flush

noncomputable def fragment0174563Chars : List Char := '[' :: (fragment0174563Chunk000Chars00 ++ fragment0174563Chunk001Chars00 ++ fragment0174563Chunk002Chars00 ++ fragment0174563Chunk003Chars00 ++ fragment0174563Chunk004Chars00)
noncomputable def fragment0174563Value : SourceJson := .arr (fragment0174563Acc00500.reverse)

theorem value_fragment0174563 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 27) (fragment0174563Chars ++ tail) =
      .ok (fragment0174563Value, tail) := by
  have hinput : fragment0174563Chars ++ tail = '[' :: (fragment0174563Chunk000Chars00 ++ (fragment0174563Chunk001Chars00 ++ (fragment0174563Chunk002Chars00 ++ (fragment0174563Chunk003Chars00 ++ (fragment0174563Chunk004Chars00 ++ (tail)))))) := by
    simp only [fragment0174563Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 27) (fragment0174563Chars ++ tail) =
        SourceJson.value (fuel + 27) ('[' :: (fragment0174563Chunk000Chars00 ++ (fragment0174563Chunk001Chars00 ++ (fragment0174563Chunk002Chars00 ++ (fragment0174563Chunk003Chars00 ++ (fragment0174563Chunk004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 27)) hinput
    _ = SourceJson.array (fuel + 26) (SourceJson.white (fragment0174563Chunk000Chars00 ++ (fragment0174563Chunk001Chars00 ++ (fragment0174563Chunk002Chars00 ++ (fragment0174563Chunk003Chars00 ++ (fragment0174563Chunk004Chars00 ++ (tail))))))) fragment0174563Acc00000 := by rfl
    _ = SourceJson.array (fuel + 24) (SourceJson.white (fragment0174563Chunk001Chars00 ++ (fragment0174563Chunk002Chars00 ++ (fragment0174563Chunk003Chars00 ++ (fragment0174563Chunk004Chars00 ++ (tail)))))) fragment0174563Acc00100 := array_fragment0174563_chunk_000 fuel (fragment0174563Chunk001Chars00 ++ (fragment0174563Chunk002Chars00 ++ (fragment0174563Chunk003Chars00 ++ (fragment0174563Chunk004Chars00 ++ (tail))))) fragment0174563Acc00000
    _ = SourceJson.array (fuel + 22) (SourceJson.white (fragment0174563Chunk002Chars00 ++ (fragment0174563Chunk003Chars00 ++ (fragment0174563Chunk004Chars00 ++ (tail))))) fragment0174563Acc00200 := array_fragment0174563_chunk_001 fuel (fragment0174563Chunk002Chars00 ++ (fragment0174563Chunk003Chars00 ++ (fragment0174563Chunk004Chars00 ++ (tail)))) fragment0174563Acc00100
    _ = SourceJson.array (fuel + 20) (SourceJson.white (fragment0174563Chunk003Chars00 ++ (fragment0174563Chunk004Chars00 ++ (tail)))) fragment0174563Acc00300 := array_fragment0174563_chunk_002 fuel (fragment0174563Chunk003Chars00 ++ (fragment0174563Chunk004Chars00 ++ (tail))) fragment0174563Acc00200
    _ = SourceJson.array (fuel + 18) (SourceJson.white (fragment0174563Chunk004Chars00 ++ (tail))) fragment0174563Acc00400 := array_fragment0174563_chunk_003 fuel (fragment0174563Chunk004Chars00 ++ (tail)) fragment0174563Acc00300
    _ = .ok (fragment0174563Value, tail) := array_fragment0174563_chunk_004 fuel (tail) fragment0174563Acc00400

noncomputable def fragment0174215Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0174215Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0174215Field000Value00 : SourceJson := .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4'])]
noncomputable def fragment0174215Acc00100 : List (String × SourceJson) := (fragment0174215Field000Key00, fragment0174215Field000Value00) :: fragment0174215Acc00000
noncomputable def fragment0174215Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0174215_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 31) (SourceJson.white (fragment0174215Field000Chars00 ++ tail)) fragment0174215Acc00000 =
      SourceJson.object (fuel + 30) (SourceJson.white tail) fragment0174215Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0174215_object_field_000"
  err.flush

noncomputable def fragment0174215Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0174215Field001Value00 : SourceJson := .number (String.ofList ['6'])
noncomputable def fragment0174215Acc00200 : List (String × SourceJson) := (fragment0174215Field001Key00, fragment0174215Field001Value00) :: fragment0174215Acc00100
noncomputable def fragment0174215Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '6', ',']

theorem object_fragment0174215_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 30) (SourceJson.white (fragment0174215Field001Chars00 ++ tail)) fragment0174215Acc00100 =
      SourceJson.object (fuel + 29) (SourceJson.white tail) fragment0174215Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0174215_object_field_001"
  err.flush

noncomputable def fragment0174215Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0174215Field002Value00 : SourceJson := .number (String.ofList ['2', '4'])
noncomputable def fragment0174215Acc00300 : List (String × SourceJson) := (fragment0174215Field002Key00, fragment0174215Field002Value00) :: fragment0174215Acc00200
noncomputable def fragment0174215Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '2', '4', ',']

theorem object_fragment0174215_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 29) (SourceJson.white (fragment0174215Field002Chars00 ++ tail)) fragment0174215Acc00200 =
      SourceJson.object (fuel + 28) (SourceJson.white tail) fragment0174215Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0174215_object_field_002"
  err.flush

noncomputable def fragment0174215Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0174215Field003Value00 : SourceJson := fragment0174563Value
noncomputable def fragment0174215Acc00400 : List (String × SourceJson) := (fragment0174215Field003Key00, fragment0174215Field003Value00) :: fragment0174215Acc00300
noncomputable def fragment0174215Field003HeaderChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ']
noncomputable def fragment0174215Field003SuffixChars00 : List Char := [',']
noncomputable def fragment0174215Field003Chars00 : List Char := fragment0174215Field003HeaderChars00 ++ fragment0174563Chars ++ fragment0174215Field003SuffixChars00

noncomputable def fragment0174215Field003AfterValue00 (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending => .ok (.obj (((fragment0174215Field003Key00, result.1) :: fragment0174215Acc00300).reverse), ending)
  | ',' :: ending => SourceJson.object fuel (SourceJson.white ending) ((fragment0174215Field003Key00, result.1) :: fragment0174215Acc00300)
  | _ => .error "object separator missing"

theorem object_fragment0174215_field_003_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 28) (SourceJson.white (fragment0174215Field003HeaderChars00 ++ rest)) fragment0174215Acc00300 =
      (SourceJson.value (fuel + 27) rest).bind (fragment0174215Field003AfterValue00 (fuel + 27)) := by rfl

theorem object_fragment0174215_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 28) (SourceJson.white (fragment0174215Field003Chars00 ++ tail)) fragment0174215Acc00300 =
      SourceJson.object (fuel + 27) (SourceJson.white tail) fragment0174215Acc00400 := by
  have hinput : fragment0174215Field003Chars00 ++ tail = fragment0174215Field003HeaderChars00 ++ (fragment0174563Chars ++ (fragment0174215Field003SuffixChars00 ++ tail)) := by
    simp only [fragment0174215Field003Chars00, List.append_assoc]
  calc
    SourceJson.object (fuel + 28) (SourceJson.white (fragment0174215Field003Chars00 ++ tail)) fragment0174215Acc00300 =
        SourceJson.object (fuel + 28)
          (SourceJson.white (fragment0174215Field003HeaderChars00 ++ (fragment0174563Chars ++ (fragment0174215Field003SuffixChars00 ++ tail)))) fragment0174215Acc00300 :=
      congrArg (fun s => SourceJson.object (fuel + 28) (SourceJson.white s) fragment0174215Acc00300) hinput
    _ = (SourceJson.value (fuel + 27) (fragment0174563Chars ++ (fragment0174215Field003SuffixChars00 ++ tail))).bind
        (fragment0174215Field003AfterValue00 (fuel + 27)) := object_fragment0174215_field_003_header fuel (fragment0174563Chars ++ (fragment0174215Field003SuffixChars00 ++ tail))
    _ = (Except.ok (fragment0174563Value, fragment0174215Field003SuffixChars00 ++ tail)).bind (fragment0174215Field003AfterValue00 (fuel + 27)) :=
      congrArg (fun result => result.bind (fragment0174215Field003AfterValue00 (fuel + 27)))
        (value_fragment0174563 (fuel + 0) (fragment0174215Field003SuffixChars00 ++ tail))
    _ = SourceJson.object (fuel + 27) (SourceJson.white tail) fragment0174215Acc00400 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0174215_object_field_003"
  err.flush

noncomputable def fragment0174215Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0174215Field004Value00 : SourceJson := .number (String.ofList ['3', '0'])
noncomputable def fragment0174215Acc00500 : List (String × SourceJson) := (fragment0174215Field004Key00, fragment0174215Field004Value00) :: fragment0174215Acc00400
noncomputable def fragment0174215Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '3', '0', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0174215_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 27) (SourceJson.white (fragment0174215Field004Chars00 ++ tail)) fragment0174215Acc00400 =
      .ok (.obj (fragment0174215Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0174215_object_field_004"
  err.flush

noncomputable def fragment0174215Chars : List Char := '{' :: (fragment0174215Field000Chars00 ++ fragment0174215Field001Chars00 ++ fragment0174215Field002Chars00 ++ fragment0174215Field003Chars00 ++ fragment0174215Field004Chars00)
noncomputable def fragment0174215Value : SourceJson := .obj (fragment0174215Acc00500.reverse)

theorem value_fragment0174215 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 32) (fragment0174215Chars ++ tail) =
      .ok (fragment0174215Value, tail) := by
  have hinput : fragment0174215Chars ++ tail = '{' :: (fragment0174215Field000Chars00 ++ (fragment0174215Field001Chars00 ++ (fragment0174215Field002Chars00 ++ (fragment0174215Field003Chars00 ++ (fragment0174215Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0174215Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 32) (fragment0174215Chars ++ tail) =
        SourceJson.value (fuel + 32) ('{' :: (fragment0174215Field000Chars00 ++ (fragment0174215Field001Chars00 ++ (fragment0174215Field002Chars00 ++ (fragment0174215Field003Chars00 ++ (fragment0174215Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 32)) hinput
    _ = SourceJson.object (fuel + 31) (SourceJson.white (fragment0174215Field000Chars00 ++ (fragment0174215Field001Chars00 ++ (fragment0174215Field002Chars00 ++ (fragment0174215Field003Chars00 ++ (fragment0174215Field004Chars00 ++ (tail))))))) fragment0174215Acc00000 := by rfl
    _ = SourceJson.object (fuel + 30) (SourceJson.white (fragment0174215Field001Chars00 ++ (fragment0174215Field002Chars00 ++ (fragment0174215Field003Chars00 ++ (fragment0174215Field004Chars00 ++ (tail)))))) fragment0174215Acc00100 := object_fragment0174215_field_000 fuel (fragment0174215Field001Chars00 ++ (fragment0174215Field002Chars00 ++ (fragment0174215Field003Chars00 ++ (fragment0174215Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 29) (SourceJson.white (fragment0174215Field002Chars00 ++ (fragment0174215Field003Chars00 ++ (fragment0174215Field004Chars00 ++ (tail))))) fragment0174215Acc00200 := object_fragment0174215_field_001 fuel (fragment0174215Field002Chars00 ++ (fragment0174215Field003Chars00 ++ (fragment0174215Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 28) (SourceJson.white (fragment0174215Field003Chars00 ++ (fragment0174215Field004Chars00 ++ (tail)))) fragment0174215Acc00300 := object_fragment0174215_field_002 fuel (fragment0174215Field003Chars00 ++ (fragment0174215Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 27) (SourceJson.white (fragment0174215Field004Chars00 ++ (tail))) fragment0174215Acc00400 := object_fragment0174215_field_003 fuel (fragment0174215Field004Chars00 ++ (tail))
    _ = .ok (fragment0174215Value, tail) := object_fragment0174215_field_004 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0008_before_reader"
  err.flush

noncomputable def chunk0008LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0008SuffixChars00 : List Char := [',']
noncomputable def chunk0008Chars00 : List Char := chunk0008LeadChars00 ++ fragment0174215Chars ++ chunk0008SuffixChars00
noncomputable def chunk0008Push00 (acc : List SourceJson) : List SourceJson := fragment0174215Value :: acc

noncomputable def chunk0008AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0008_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 90)
      (SourceJson.white (chunk0008LeadChars00 ++ (fragment0174215Chars ++ rest))) acc =
      (SourceJson.value (fuel + 89) (fragment0174215Chars ++ rest)).bind
        (chunk0008AfterValue00 (fuel + 89) acc) := by rfl

theorem array_chunk0008 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 90) (SourceJson.white (chunk0008Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 89) (SourceJson.white tail) (chunk0008Push00 acc) := by
  have hinput : chunk0008Chars00 ++ tail = chunk0008LeadChars00 ++ (fragment0174215Chars ++ (chunk0008SuffixChars00 ++ tail)) := by
    simp only [chunk0008Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 90) (SourceJson.white (chunk0008Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 90)
          (SourceJson.white (chunk0008LeadChars00 ++ (fragment0174215Chars ++ (chunk0008SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 90) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 89) (fragment0174215Chars ++ (chunk0008SuffixChars00 ++ tail))).bind
        (chunk0008AfterValue00 (fuel + 89) acc) := array_chunk0008_head fuel (chunk0008SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0174215Value, chunk0008SuffixChars00 ++ tail)).bind
        (chunk0008AfterValue00 (fuel + 89) acc) :=
      congrArg (fun result => result.bind (chunk0008AfterValue00 (fuel + 89) acc))
        (value_fragment0174215 (fuel + 57) (chunk0008SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 89) (SourceJson.white tail) (chunk0008Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0008_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0008Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0008Push00 (acc)

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 90) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 89) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0008Chars00 ++ (tail) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 90) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 90) (SourceJson.white (chunk0008Chars00 ++ (tail))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 90) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 89) (SourceJson.white tail) (blockPush acc) := array_chunk0008 fuel (tail) (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 174209).take 2345 = blockChars := by rfl

theorem block_original_split : sourceRest 174209 = blockChars ++ sourceRest 176554 := by
  calc
    sourceRest 174209 = (sourceRest 174209).take 2345 ++ (sourceRest 174209).drop 2345 :=
      (List.take_append_drop 2345 (sourceRest 174209)).symm
    _ = blockChars ++ (sourceRest 174209).drop 2345 :=
      congrArg (fun part => part ++ (sourceRest 174209).drop 2345) block_original_prefix
    _ = blockChars ++ sourceRest 176554 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 174209 2345)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 90) (SourceJson.white (sourceRest 174209)) acc =
      SourceJson.array (fuel + 89) (SourceJson.white (sourceRest 176554)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 90) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 176554) acc)

#print axioms array_fragment0174563_chunk_000
#print axioms array_fragment0174563_chunk_001
#print axioms array_fragment0174563_chunk_002
#print axioms array_fragment0174563_chunk_003
#print axioms array_fragment0174563_chunk_004
#print axioms value_fragment0174563
#print axioms object_fragment0174215_field_000
#print axioms object_fragment0174215_field_001
#print axioms object_fragment0174215_field_002
#print axioms object_fragment0174215_field_003_header
#print axioms object_fragment0174215_field_003
#print axioms object_fragment0174215_field_004
#print axioms value_fragment0174215
#print axioms array_chunk0008_head
#print axioms array_chunk0008
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end FaceLedgerBlock005

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
