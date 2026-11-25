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

namespace FaceLedgerBlock003

noncomputable def fragment0167582Acc00000 : List SourceJson := []

noncomputable def fragment0167582Chunk000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0167582Chunk000Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '7']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '7']), .number (String.ofList ['2', '9'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '7']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '8'])]) :: (acc))

theorem array_fragment0167582_chunk_000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 26) (SourceJson.white (fragment0167582Chunk000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 24) (SourceJson.white tail) (fragment0167582Chunk000Push00 acc) := by
  rfl

noncomputable def fragment0167582Acc00100 : List SourceJson := fragment0167582Chunk000Push00 fragment0167582Acc00000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0167582_array_chunk_000"
  err.flush

noncomputable def fragment0167582Chunk001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0167582Chunk001Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['7']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '7']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '9'])]) :: (acc))

theorem array_fragment0167582_chunk_001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 24) (SourceJson.white (fragment0167582Chunk001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 22) (SourceJson.white tail) (fragment0167582Chunk001Push00 acc) := by
  rfl

noncomputable def fragment0167582Acc00200 : List SourceJson := fragment0167582Chunk001Push00 fragment0167582Acc00100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0167582_array_chunk_001"
  err.flush

noncomputable def fragment0167582Chunk002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0167582Chunk002Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['9']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '7']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '7'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '7']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '7']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '9'])]) :: (acc))

theorem array_fragment0167582_chunk_002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 22) (SourceJson.white (fragment0167582Chunk002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 20) (SourceJson.white tail) (fragment0167582Chunk002Push00 acc) := by
  rfl

noncomputable def fragment0167582Acc00300 : List SourceJson := fragment0167582Chunk002Push00 fragment0167582Acc00200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0167582_array_chunk_002"
  err.flush

noncomputable def fragment0167582Chunk003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0167582Chunk003Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '7']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '7']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '9'])]) :: ((.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '3']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '9'])]) :: (acc))

theorem array_fragment0167582_chunk_003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 20) (SourceJson.white (fragment0167582Chunk003Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 18) (SourceJson.white tail) (fragment0167582Chunk003Push00 acc) := by
  rfl

noncomputable def fragment0167582Acc00400 : List SourceJson := fragment0167582Chunk003Push00 fragment0167582Acc00300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0167582_array_chunk_003"
  err.flush

noncomputable def fragment0167582Chunk004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']']
noncomputable def fragment0167582Chunk004Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '7']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '7']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '9'])]) :: (acc)

theorem array_fragment0167582_chunk_004 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 18) (SourceJson.white (fragment0167582Chunk004Chars00 ++ tail)) acc =
      .ok (.arr ((fragment0167582Chunk004Push00 acc).reverse), tail) := by
  rfl

noncomputable def fragment0167582Acc00500 : List SourceJson := fragment0167582Chunk004Push00 fragment0167582Acc00400

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0167582_array_chunk_004"
  err.flush

noncomputable def fragment0167582Chars : List Char := '[' :: (fragment0167582Chunk000Chars00 ++ fragment0167582Chunk001Chars00 ++ fragment0167582Chunk002Chars00 ++ fragment0167582Chunk003Chars00 ++ fragment0167582Chunk004Chars00)
noncomputable def fragment0167582Value : SourceJson := .arr (fragment0167582Acc00500.reverse)

theorem value_fragment0167582 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 27) (fragment0167582Chars ++ tail) =
      .ok (fragment0167582Value, tail) := by
  have hinput : fragment0167582Chars ++ tail = '[' :: (fragment0167582Chunk000Chars00 ++ (fragment0167582Chunk001Chars00 ++ (fragment0167582Chunk002Chars00 ++ (fragment0167582Chunk003Chars00 ++ (fragment0167582Chunk004Chars00 ++ (tail)))))) := by
    simp only [fragment0167582Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 27) (fragment0167582Chars ++ tail) =
        SourceJson.value (fuel + 27) ('[' :: (fragment0167582Chunk000Chars00 ++ (fragment0167582Chunk001Chars00 ++ (fragment0167582Chunk002Chars00 ++ (fragment0167582Chunk003Chars00 ++ (fragment0167582Chunk004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 27)) hinput
    _ = SourceJson.array (fuel + 26) (SourceJson.white (fragment0167582Chunk000Chars00 ++ (fragment0167582Chunk001Chars00 ++ (fragment0167582Chunk002Chars00 ++ (fragment0167582Chunk003Chars00 ++ (fragment0167582Chunk004Chars00 ++ (tail))))))) fragment0167582Acc00000 := by rfl
    _ = SourceJson.array (fuel + 24) (SourceJson.white (fragment0167582Chunk001Chars00 ++ (fragment0167582Chunk002Chars00 ++ (fragment0167582Chunk003Chars00 ++ (fragment0167582Chunk004Chars00 ++ (tail)))))) fragment0167582Acc00100 := array_fragment0167582_chunk_000 fuel (fragment0167582Chunk001Chars00 ++ (fragment0167582Chunk002Chars00 ++ (fragment0167582Chunk003Chars00 ++ (fragment0167582Chunk004Chars00 ++ (tail))))) fragment0167582Acc00000
    _ = SourceJson.array (fuel + 22) (SourceJson.white (fragment0167582Chunk002Chars00 ++ (fragment0167582Chunk003Chars00 ++ (fragment0167582Chunk004Chars00 ++ (tail))))) fragment0167582Acc00200 := array_fragment0167582_chunk_001 fuel (fragment0167582Chunk002Chars00 ++ (fragment0167582Chunk003Chars00 ++ (fragment0167582Chunk004Chars00 ++ (tail)))) fragment0167582Acc00100
    _ = SourceJson.array (fuel + 20) (SourceJson.white (fragment0167582Chunk003Chars00 ++ (fragment0167582Chunk004Chars00 ++ (tail)))) fragment0167582Acc00300 := array_fragment0167582_chunk_002 fuel (fragment0167582Chunk003Chars00 ++ (fragment0167582Chunk004Chars00 ++ (tail))) fragment0167582Acc00200
    _ = SourceJson.array (fuel + 18) (SourceJson.white (fragment0167582Chunk004Chars00 ++ (tail))) fragment0167582Acc00400 := array_fragment0167582_chunk_003 fuel (fragment0167582Chunk004Chars00 ++ (tail)) fragment0167582Acc00300
    _ = .ok (fragment0167582Value, tail) := array_fragment0167582_chunk_004 fuel (tail) fragment0167582Acc00400

noncomputable def fragment0167236Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0167236Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0167236Field000Value00 : SourceJson := .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '7']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '7']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '9'])]
noncomputable def fragment0167236Acc00100 : List (String × SourceJson) := (fragment0167236Field000Key00, fragment0167236Field000Value00) :: fragment0167236Acc00000
noncomputable def fragment0167236Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0167236_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 31) (SourceJson.white (fragment0167236Field000Chars00 ++ tail)) fragment0167236Acc00000 =
      SourceJson.object (fuel + 30) (SourceJson.white tail) fragment0167236Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0167236_object_field_000"
  err.flush

noncomputable def fragment0167236Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0167236Field001Value00 : SourceJson := .number (String.ofList ['6'])
noncomputable def fragment0167236Acc00200 : List (String × SourceJson) := (fragment0167236Field001Key00, fragment0167236Field001Value00) :: fragment0167236Acc00100
noncomputable def fragment0167236Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '6', ',']

theorem object_fragment0167236_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 30) (SourceJson.white (fragment0167236Field001Chars00 ++ tail)) fragment0167236Acc00100 =
      SourceJson.object (fuel + 29) (SourceJson.white tail) fragment0167236Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0167236_object_field_001"
  err.flush

noncomputable def fragment0167236Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0167236Field002Value00 : SourceJson := .number (String.ofList ['2', '9'])
noncomputable def fragment0167236Acc00300 : List (String × SourceJson) := (fragment0167236Field002Key00, fragment0167236Field002Value00) :: fragment0167236Acc00200
noncomputable def fragment0167236Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '2', '9', ',']

theorem object_fragment0167236_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 29) (SourceJson.white (fragment0167236Field002Chars00 ++ tail)) fragment0167236Acc00200 =
      SourceJson.object (fuel + 28) (SourceJson.white tail) fragment0167236Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0167236_object_field_002"
  err.flush

noncomputable def fragment0167236Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0167236Field003Value00 : SourceJson := fragment0167582Value
noncomputable def fragment0167236Acc00400 : List (String × SourceJson) := (fragment0167236Field003Key00, fragment0167236Field003Value00) :: fragment0167236Acc00300
noncomputable def fragment0167236Field003HeaderChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ']
noncomputable def fragment0167236Field003SuffixChars00 : List Char := [',']
noncomputable def fragment0167236Field003Chars00 : List Char := fragment0167236Field003HeaderChars00 ++ fragment0167582Chars ++ fragment0167236Field003SuffixChars00

noncomputable def fragment0167236Field003AfterValue00 (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending => .ok (.obj (((fragment0167236Field003Key00, result.1) :: fragment0167236Acc00300).reverse), ending)
  | ',' :: ending => SourceJson.object fuel (SourceJson.white ending) ((fragment0167236Field003Key00, result.1) :: fragment0167236Acc00300)
  | _ => .error "object separator missing"

theorem object_fragment0167236_field_003_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 28) (SourceJson.white (fragment0167236Field003HeaderChars00 ++ rest)) fragment0167236Acc00300 =
      (SourceJson.value (fuel + 27) rest).bind (fragment0167236Field003AfterValue00 (fuel + 27)) := by rfl

theorem object_fragment0167236_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 28) (SourceJson.white (fragment0167236Field003Chars00 ++ tail)) fragment0167236Acc00300 =
      SourceJson.object (fuel + 27) (SourceJson.white tail) fragment0167236Acc00400 := by
  have hinput : fragment0167236Field003Chars00 ++ tail = fragment0167236Field003HeaderChars00 ++ (fragment0167582Chars ++ (fragment0167236Field003SuffixChars00 ++ tail)) := by
    simp only [fragment0167236Field003Chars00, List.append_assoc]
  calc
    SourceJson.object (fuel + 28) (SourceJson.white (fragment0167236Field003Chars00 ++ tail)) fragment0167236Acc00300 =
        SourceJson.object (fuel + 28)
          (SourceJson.white (fragment0167236Field003HeaderChars00 ++ (fragment0167582Chars ++ (fragment0167236Field003SuffixChars00 ++ tail)))) fragment0167236Acc00300 :=
      congrArg (fun s => SourceJson.object (fuel + 28) (SourceJson.white s) fragment0167236Acc00300) hinput
    _ = (SourceJson.value (fuel + 27) (fragment0167582Chars ++ (fragment0167236Field003SuffixChars00 ++ tail))).bind
        (fragment0167236Field003AfterValue00 (fuel + 27)) := object_fragment0167236_field_003_header fuel (fragment0167582Chars ++ (fragment0167236Field003SuffixChars00 ++ tail))
    _ = (Except.ok (fragment0167582Value, fragment0167236Field003SuffixChars00 ++ tail)).bind (fragment0167236Field003AfterValue00 (fuel + 27)) :=
      congrArg (fun result => result.bind (fragment0167236Field003AfterValue00 (fuel + 27)))
        (value_fragment0167582 (fuel + 0) (fragment0167236Field003SuffixChars00 ++ tail))
    _ = SourceJson.object (fuel + 27) (SourceJson.white tail) fragment0167236Acc00400 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0167236_object_field_003"
  err.flush

noncomputable def fragment0167236Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0167236Field004Value00 : SourceJson := .number (String.ofList ['3', '0'])
noncomputable def fragment0167236Acc00500 : List (String × SourceJson) := (fragment0167236Field004Key00, fragment0167236Field004Value00) :: fragment0167236Acc00400
noncomputable def fragment0167236Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '3', '0', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0167236_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 27) (SourceJson.white (fragment0167236Field004Chars00 ++ tail)) fragment0167236Acc00400 =
      .ok (.obj (fragment0167236Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0167236_object_field_004"
  err.flush

noncomputable def fragment0167236Chars : List Char := '{' :: (fragment0167236Field000Chars00 ++ fragment0167236Field001Chars00 ++ fragment0167236Field002Chars00 ++ fragment0167236Field003Chars00 ++ fragment0167236Field004Chars00)
noncomputable def fragment0167236Value : SourceJson := .obj (fragment0167236Acc00500.reverse)

theorem value_fragment0167236 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 32) (fragment0167236Chars ++ tail) =
      .ok (fragment0167236Value, tail) := by
  have hinput : fragment0167236Chars ++ tail = '{' :: (fragment0167236Field000Chars00 ++ (fragment0167236Field001Chars00 ++ (fragment0167236Field002Chars00 ++ (fragment0167236Field003Chars00 ++ (fragment0167236Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0167236Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 32) (fragment0167236Chars ++ tail) =
        SourceJson.value (fuel + 32) ('{' :: (fragment0167236Field000Chars00 ++ (fragment0167236Field001Chars00 ++ (fragment0167236Field002Chars00 ++ (fragment0167236Field003Chars00 ++ (fragment0167236Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 32)) hinput
    _ = SourceJson.object (fuel + 31) (SourceJson.white (fragment0167236Field000Chars00 ++ (fragment0167236Field001Chars00 ++ (fragment0167236Field002Chars00 ++ (fragment0167236Field003Chars00 ++ (fragment0167236Field004Chars00 ++ (tail))))))) fragment0167236Acc00000 := by rfl
    _ = SourceJson.object (fuel + 30) (SourceJson.white (fragment0167236Field001Chars00 ++ (fragment0167236Field002Chars00 ++ (fragment0167236Field003Chars00 ++ (fragment0167236Field004Chars00 ++ (tail)))))) fragment0167236Acc00100 := object_fragment0167236_field_000 fuel (fragment0167236Field001Chars00 ++ (fragment0167236Field002Chars00 ++ (fragment0167236Field003Chars00 ++ (fragment0167236Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 29) (SourceJson.white (fragment0167236Field002Chars00 ++ (fragment0167236Field003Chars00 ++ (fragment0167236Field004Chars00 ++ (tail))))) fragment0167236Acc00200 := object_fragment0167236_field_001 fuel (fragment0167236Field002Chars00 ++ (fragment0167236Field003Chars00 ++ (fragment0167236Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 28) (SourceJson.white (fragment0167236Field003Chars00 ++ (fragment0167236Field004Chars00 ++ (tail)))) fragment0167236Acc00300 := object_fragment0167236_field_002 fuel (fragment0167236Field003Chars00 ++ (fragment0167236Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 27) (SourceJson.white (fragment0167236Field004Chars00 ++ (tail))) fragment0167236Acc00400 := object_fragment0167236_field_003 fuel (fragment0167236Field004Chars00 ++ (tail))
    _ = .ok (fragment0167236Value, tail) := object_fragment0167236_field_004 fuel (tail)

noncomputable def fragment0169862Acc00000 : List SourceJson := []

noncomputable def fragment0169862Chunk000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0169862Chunk000Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['7']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '8'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['8']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '7']), .number (String.ofList ['2', '5'])]) :: (acc))

theorem array_fragment0169862_chunk_000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 21) (SourceJson.white (fragment0169862Chunk000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 19) (SourceJson.white tail) (fragment0169862Chunk000Push00 acc) := by
  rfl

noncomputable def fragment0169862Acc00100 : List SourceJson := fragment0169862Chunk000Push00 fragment0169862Acc00000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0169862_array_chunk_000"
  err.flush

noncomputable def fragment0169862Chunk001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0169862Chunk001Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '7']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '8'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '0'])]) :: (acc))

theorem array_fragment0169862_chunk_001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 19) (SourceJson.white (fragment0169862Chunk001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 17) (SourceJson.white tail) (fragment0169862Chunk001Push00 acc) := by
  rfl

noncomputable def fragment0169862Acc00200 : List SourceJson := fragment0169862Chunk001Push00 fragment0169862Acc00100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0169862_array_chunk_001"
  err.flush

noncomputable def fragment0169862Chunk002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0169862Chunk002Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '3']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '8'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '7']), .number (String.ofList ['2', '6'])]) :: (acc))

theorem array_fragment0169862_chunk_002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 17) (SourceJson.white (fragment0169862Chunk002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 15) (SourceJson.white tail) (fragment0169862Chunk002Push00 acc) := by
  rfl

noncomputable def fragment0169862Acc00300 : List SourceJson := fragment0169862Chunk002Push00 fragment0169862Acc00200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0169862_array_chunk_002"
  err.flush

noncomputable def fragment0169862Chunk003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']']
noncomputable def fragment0169862Chunk003Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '7']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '8'])]) :: ((.arr [.number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '7']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '8'])]) :: (acc))

theorem array_fragment0169862_chunk_003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 15) (SourceJson.white (fragment0169862Chunk003Chars00 ++ tail)) acc =
      .ok (.arr ((fragment0169862Chunk003Push00 acc).reverse), tail) := by
  rfl

noncomputable def fragment0169862Acc00400 : List SourceJson := fragment0169862Chunk003Push00 fragment0169862Acc00300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0169862_array_chunk_003"
  err.flush

noncomputable def fragment0169862Chars : List Char := '[' :: (fragment0169862Chunk000Chars00 ++ fragment0169862Chunk001Chars00 ++ fragment0169862Chunk002Chars00 ++ fragment0169862Chunk003Chars00)
noncomputable def fragment0169862Value : SourceJson := .arr (fragment0169862Acc00400.reverse)

theorem value_fragment0169862 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 22) (fragment0169862Chars ++ tail) =
      .ok (fragment0169862Value, tail) := by
  have hinput : fragment0169862Chars ++ tail = '[' :: (fragment0169862Chunk000Chars00 ++ (fragment0169862Chunk001Chars00 ++ (fragment0169862Chunk002Chars00 ++ (fragment0169862Chunk003Chars00 ++ (tail))))) := by
    simp only [fragment0169862Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 22) (fragment0169862Chars ++ tail) =
        SourceJson.value (fuel + 22) ('[' :: (fragment0169862Chunk000Chars00 ++ (fragment0169862Chunk001Chars00 ++ (fragment0169862Chunk002Chars00 ++ (fragment0169862Chunk003Chars00 ++ (tail)))))) :=
      congrArg (SourceJson.value (fuel + 22)) hinput
    _ = SourceJson.array (fuel + 21) (SourceJson.white (fragment0169862Chunk000Chars00 ++ (fragment0169862Chunk001Chars00 ++ (fragment0169862Chunk002Chars00 ++ (fragment0169862Chunk003Chars00 ++ (tail)))))) fragment0169862Acc00000 := by rfl
    _ = SourceJson.array (fuel + 19) (SourceJson.white (fragment0169862Chunk001Chars00 ++ (fragment0169862Chunk002Chars00 ++ (fragment0169862Chunk003Chars00 ++ (tail))))) fragment0169862Acc00100 := array_fragment0169862_chunk_000 fuel (fragment0169862Chunk001Chars00 ++ (fragment0169862Chunk002Chars00 ++ (fragment0169862Chunk003Chars00 ++ (tail)))) fragment0169862Acc00000
    _ = SourceJson.array (fuel + 17) (SourceJson.white (fragment0169862Chunk002Chars00 ++ (fragment0169862Chunk003Chars00 ++ (tail)))) fragment0169862Acc00200 := array_fragment0169862_chunk_001 fuel (fragment0169862Chunk002Chars00 ++ (fragment0169862Chunk003Chars00 ++ (tail))) fragment0169862Acc00100
    _ = SourceJson.array (fuel + 15) (SourceJson.white (fragment0169862Chunk003Chars00 ++ (tail))) fragment0169862Acc00300 := array_fragment0169862_chunk_002 fuel (fragment0169862Chunk003Chars00 ++ (tail)) fragment0169862Acc00200
    _ = .ok (fragment0169862Value, tail) := array_fragment0169862_chunk_003 fuel (tail) fragment0169862Acc00300

noncomputable def fragment0169567Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0169567Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0169567Field000Value00 : SourceJson := .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '7']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '8'])]
noncomputable def fragment0169567Acc00100 : List (String × SourceJson) := (fragment0169567Field000Key00, fragment0169567Field000Value00) :: fragment0169567Acc00000
noncomputable def fragment0169567Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0169567_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 26) (SourceJson.white (fragment0169567Field000Chars00 ++ tail)) fragment0169567Acc00000 =
      SourceJson.object (fuel + 25) (SourceJson.white tail) fragment0169567Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0169567_object_field_000"
  err.flush

noncomputable def fragment0169567Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0169567Field001Value00 : SourceJson := .number (String.ofList ['5'])
noncomputable def fragment0169567Acc00200 : List (String × SourceJson) := (fragment0169567Field001Key00, fragment0169567Field001Value00) :: fragment0169567Acc00100
noncomputable def fragment0169567Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '5', ',']

theorem object_fragment0169567_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 25) (SourceJson.white (fragment0169567Field001Chars00 ++ tail)) fragment0169567Acc00100 =
      SourceJson.object (fuel + 24) (SourceJson.white tail) fragment0169567Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0169567_object_field_001"
  err.flush

noncomputable def fragment0169567Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0169567Field002Value00 : SourceJson := .number (String.ofList ['2', '8'])
noncomputable def fragment0169567Acc00300 : List (String × SourceJson) := (fragment0169567Field002Key00, fragment0169567Field002Value00) :: fragment0169567Acc00200
noncomputable def fragment0169567Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '2', '8', ',']

theorem object_fragment0169567_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 24) (SourceJson.white (fragment0169567Field002Chars00 ++ tail)) fragment0169567Acc00200 =
      SourceJson.object (fuel + 23) (SourceJson.white tail) fragment0169567Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0169567_object_field_002"
  err.flush

noncomputable def fragment0169567Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0169567Field003Value00 : SourceJson := fragment0169862Value
noncomputable def fragment0169567Acc00400 : List (String × SourceJson) := (fragment0169567Field003Key00, fragment0169567Field003Value00) :: fragment0169567Acc00300
noncomputable def fragment0169567Field003HeaderChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ']
noncomputable def fragment0169567Field003SuffixChars00 : List Char := [',']
noncomputable def fragment0169567Field003Chars00 : List Char := fragment0169567Field003HeaderChars00 ++ fragment0169862Chars ++ fragment0169567Field003SuffixChars00

noncomputable def fragment0169567Field003AfterValue00 (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending => .ok (.obj (((fragment0169567Field003Key00, result.1) :: fragment0169567Acc00300).reverse), ending)
  | ',' :: ending => SourceJson.object fuel (SourceJson.white ending) ((fragment0169567Field003Key00, result.1) :: fragment0169567Acc00300)
  | _ => .error "object separator missing"

theorem object_fragment0169567_field_003_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 23) (SourceJson.white (fragment0169567Field003HeaderChars00 ++ rest)) fragment0169567Acc00300 =
      (SourceJson.value (fuel + 22) rest).bind (fragment0169567Field003AfterValue00 (fuel + 22)) := by rfl

theorem object_fragment0169567_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 23) (SourceJson.white (fragment0169567Field003Chars00 ++ tail)) fragment0169567Acc00300 =
      SourceJson.object (fuel + 22) (SourceJson.white tail) fragment0169567Acc00400 := by
  have hinput : fragment0169567Field003Chars00 ++ tail = fragment0169567Field003HeaderChars00 ++ (fragment0169862Chars ++ (fragment0169567Field003SuffixChars00 ++ tail)) := by
    simp only [fragment0169567Field003Chars00, List.append_assoc]
  calc
    SourceJson.object (fuel + 23) (SourceJson.white (fragment0169567Field003Chars00 ++ tail)) fragment0169567Acc00300 =
        SourceJson.object (fuel + 23)
          (SourceJson.white (fragment0169567Field003HeaderChars00 ++ (fragment0169862Chars ++ (fragment0169567Field003SuffixChars00 ++ tail)))) fragment0169567Acc00300 :=
      congrArg (fun s => SourceJson.object (fuel + 23) (SourceJson.white s) fragment0169567Acc00300) hinput
    _ = (SourceJson.value (fuel + 22) (fragment0169862Chars ++ (fragment0169567Field003SuffixChars00 ++ tail))).bind
        (fragment0169567Field003AfterValue00 (fuel + 22)) := object_fragment0169567_field_003_header fuel (fragment0169862Chars ++ (fragment0169567Field003SuffixChars00 ++ tail))
    _ = (Except.ok (fragment0169862Value, fragment0169567Field003SuffixChars00 ++ tail)).bind (fragment0169567Field003AfterValue00 (fuel + 22)) :=
      congrArg (fun result => result.bind (fragment0169567Field003AfterValue00 (fuel + 22)))
        (value_fragment0169862 (fuel + 0) (fragment0169567Field003SuffixChars00 ++ tail))
    _ = SourceJson.object (fuel + 22) (SourceJson.white tail) fragment0169567Acc00400 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0169567_object_field_003"
  err.flush

noncomputable def fragment0169567Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0169567Field004Value00 : SourceJson := .number (String.ofList ['2', '0'])
noncomputable def fragment0169567Acc00500 : List (String × SourceJson) := (fragment0169567Field004Key00, fragment0169567Field004Value00) :: fragment0169567Acc00400
noncomputable def fragment0169567Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '2', '0', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0169567_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 22) (SourceJson.white (fragment0169567Field004Chars00 ++ tail)) fragment0169567Acc00400 =
      .ok (.obj (fragment0169567Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0169567_object_field_004"
  err.flush

noncomputable def fragment0169567Chars : List Char := '{' :: (fragment0169567Field000Chars00 ++ fragment0169567Field001Chars00 ++ fragment0169567Field002Chars00 ++ fragment0169567Field003Chars00 ++ fragment0169567Field004Chars00)
noncomputable def fragment0169567Value : SourceJson := .obj (fragment0169567Acc00500.reverse)

theorem value_fragment0169567 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 27) (fragment0169567Chars ++ tail) =
      .ok (fragment0169567Value, tail) := by
  have hinput : fragment0169567Chars ++ tail = '{' :: (fragment0169567Field000Chars00 ++ (fragment0169567Field001Chars00 ++ (fragment0169567Field002Chars00 ++ (fragment0169567Field003Chars00 ++ (fragment0169567Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0169567Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 27) (fragment0169567Chars ++ tail) =
        SourceJson.value (fuel + 27) ('{' :: (fragment0169567Field000Chars00 ++ (fragment0169567Field001Chars00 ++ (fragment0169567Field002Chars00 ++ (fragment0169567Field003Chars00 ++ (fragment0169567Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 27)) hinput
    _ = SourceJson.object (fuel + 26) (SourceJson.white (fragment0169567Field000Chars00 ++ (fragment0169567Field001Chars00 ++ (fragment0169567Field002Chars00 ++ (fragment0169567Field003Chars00 ++ (fragment0169567Field004Chars00 ++ (tail))))))) fragment0169567Acc00000 := by rfl
    _ = SourceJson.object (fuel + 25) (SourceJson.white (fragment0169567Field001Chars00 ++ (fragment0169567Field002Chars00 ++ (fragment0169567Field003Chars00 ++ (fragment0169567Field004Chars00 ++ (tail)))))) fragment0169567Acc00100 := object_fragment0169567_field_000 fuel (fragment0169567Field001Chars00 ++ (fragment0169567Field002Chars00 ++ (fragment0169567Field003Chars00 ++ (fragment0169567Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 24) (SourceJson.white (fragment0169567Field002Chars00 ++ (fragment0169567Field003Chars00 ++ (fragment0169567Field004Chars00 ++ (tail))))) fragment0169567Acc00200 := object_fragment0169567_field_001 fuel (fragment0169567Field002Chars00 ++ (fragment0169567Field003Chars00 ++ (fragment0169567Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 23) (SourceJson.white (fragment0169567Field003Chars00 ++ (fragment0169567Field004Chars00 ++ (tail)))) fragment0169567Acc00300 := object_fragment0169567_field_002 fuel (fragment0169567Field003Chars00 ++ (fragment0169567Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 22) (SourceJson.white (fragment0169567Field004Chars00 ++ (tail))) fragment0169567Acc00400 := object_fragment0169567_field_003 fuel (fragment0169567Field004Chars00 ++ (tail))
    _ = .ok (fragment0169567Value, tail) := object_fragment0169567_field_004 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0003_before_reader"
  err.flush

noncomputable def chunk0003LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0003SuffixChars00 : List Char := [',']
noncomputable def chunk0003Chars00 : List Char := chunk0003LeadChars00 ++ fragment0167236Chars ++ chunk0003SuffixChars00
noncomputable def chunk0003Push00 (acc : List SourceJson) : List SourceJson := fragment0167236Value :: acc

noncomputable def chunk0003AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0003_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 95)
      (SourceJson.white (chunk0003LeadChars00 ++ (fragment0167236Chars ++ rest))) acc =
      (SourceJson.value (fuel + 94) (fragment0167236Chars ++ rest)).bind
        (chunk0003AfterValue00 (fuel + 94) acc) := by rfl

theorem array_chunk0003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 95) (SourceJson.white (chunk0003Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 94) (SourceJson.white tail) (chunk0003Push00 acc) := by
  have hinput : chunk0003Chars00 ++ tail = chunk0003LeadChars00 ++ (fragment0167236Chars ++ (chunk0003SuffixChars00 ++ tail)) := by
    simp only [chunk0003Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 95) (SourceJson.white (chunk0003Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 95)
          (SourceJson.white (chunk0003LeadChars00 ++ (fragment0167236Chars ++ (chunk0003SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 95) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 94) (fragment0167236Chars ++ (chunk0003SuffixChars00 ++ tail))).bind
        (chunk0003AfterValue00 (fuel + 94) acc) := array_chunk0003_head fuel (chunk0003SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0167236Value, chunk0003SuffixChars00 ++ tail)).bind
        (chunk0003AfterValue00 (fuel + 94) acc) :=
      congrArg (fun result => result.bind (chunk0003AfterValue00 (fuel + 94) acc))
        (value_fragment0167236 (fuel + 62) (chunk0003SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 94) (SourceJson.white tail) (chunk0003Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0003_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0004_before_reader"
  err.flush

noncomputable def chunk0004LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0004SuffixChars00 : List Char := [',']
noncomputable def chunk0004Chars00 : List Char := chunk0004LeadChars00 ++ fragment0169567Chars ++ chunk0004SuffixChars00
noncomputable def chunk0004Push00 (acc : List SourceJson) : List SourceJson := fragment0169567Value :: acc

noncomputable def chunk0004AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0004_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 94)
      (SourceJson.white (chunk0004LeadChars00 ++ (fragment0169567Chars ++ rest))) acc =
      (SourceJson.value (fuel + 93) (fragment0169567Chars ++ rest)).bind
        (chunk0004AfterValue00 (fuel + 93) acc) := by rfl

theorem array_chunk0004 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 94) (SourceJson.white (chunk0004Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 93) (SourceJson.white tail) (chunk0004Push00 acc) := by
  have hinput : chunk0004Chars00 ++ tail = chunk0004LeadChars00 ++ (fragment0169567Chars ++ (chunk0004SuffixChars00 ++ tail)) := by
    simp only [chunk0004Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 94) (SourceJson.white (chunk0004Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 94)
          (SourceJson.white (chunk0004LeadChars00 ++ (fragment0169567Chars ++ (chunk0004SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 94) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 93) (fragment0169567Chars ++ (chunk0004SuffixChars00 ++ tail))).bind
        (chunk0004AfterValue00 (fuel + 93) acc) := array_chunk0004_head fuel (chunk0004SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0169567Value, chunk0004SuffixChars00 ++ tail)).bind
        (chunk0004AfterValue00 (fuel + 93) acc) :=
      congrArg (fun result => result.bind (chunk0004AfterValue00 (fuel + 93) acc))
        (value_fragment0169567 (fuel + 66) (chunk0004SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 93) (SourceJson.white tail) (chunk0004Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0004_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0003Chars00 ++ chunk0004Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0004Push00 (chunk0003Push00 (acc))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 95) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 93) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0003Chars00 ++ (chunk0004Chars00 ++ (tail)) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 95) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 95) (SourceJson.white (chunk0003Chars00 ++ (chunk0004Chars00 ++ (tail)))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 95) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 94) (SourceJson.white (chunk0004Chars00 ++ (tail))) (chunk0003Push00 (acc)) := array_chunk0003 fuel (chunk0004Chars00 ++ (tail)) (acc)
    _ = SourceJson.array (fuel + 93) (SourceJson.white tail) (blockPush acc) := array_chunk0004 fuel (tail) (chunk0003Push00 (acc))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 167230).take 4004 = blockChars := by rfl

theorem block_original_split : sourceRest 167230 = blockChars ++ sourceRest 171234 := by
  calc
    sourceRest 167230 = (sourceRest 167230).take 4004 ++ (sourceRest 167230).drop 4004 :=
      (List.take_append_drop 4004 (sourceRest 167230)).symm
    _ = blockChars ++ (sourceRest 167230).drop 4004 :=
      congrArg (fun part => part ++ (sourceRest 167230).drop 4004) block_original_prefix
    _ = blockChars ++ sourceRest 171234 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 167230 4004)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 95) (SourceJson.white (sourceRest 167230)) acc =
      SourceJson.array (fuel + 93) (SourceJson.white (sourceRest 171234)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 95) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 171234) acc)

#print axioms array_fragment0167582_chunk_000
#print axioms array_fragment0167582_chunk_001
#print axioms array_fragment0167582_chunk_002
#print axioms array_fragment0167582_chunk_003
#print axioms array_fragment0167582_chunk_004
#print axioms value_fragment0167582
#print axioms object_fragment0167236_field_000
#print axioms object_fragment0167236_field_001
#print axioms object_fragment0167236_field_002
#print axioms object_fragment0167236_field_003_header
#print axioms object_fragment0167236_field_003
#print axioms object_fragment0167236_field_004
#print axioms value_fragment0167236
#print axioms array_fragment0169862_chunk_000
#print axioms array_fragment0169862_chunk_001
#print axioms array_fragment0169862_chunk_002
#print axioms array_fragment0169862_chunk_003
#print axioms value_fragment0169862
#print axioms object_fragment0169567_field_000
#print axioms object_fragment0169567_field_001
#print axioms object_fragment0169567_field_002
#print axioms object_fragment0169567_field_003_header
#print axioms object_fragment0169567_field_003
#print axioms object_fragment0169567_field_004
#print axioms value_fragment0169567
#print axioms array_chunk0003_head
#print axioms array_chunk0003
#print axioms array_chunk0004_head
#print axioms array_chunk0004
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end FaceLedgerBlock003

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
