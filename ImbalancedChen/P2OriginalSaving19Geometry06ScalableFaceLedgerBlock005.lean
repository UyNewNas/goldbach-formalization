import ImbalancedChen.P2OriginalSaving19Geometry06ScalableInput

/-! Original face_ledger grouped chunk transitions, including exact compact-input binding.
The original packed input, original parser and original decoder are unchanged.
This is a source-only candidate until normal, kernel and full-owned checks pass. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

namespace FaceLedgerBlock005

noncomputable def fragment0112954Acc00000 : List SourceJson := []

noncomputable def fragment0112954Chunk000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0112954Chunk000Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['7']), .number (String.ofList ['9']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '8']), .number (String.ofList ['3', '0'])]) :: ((.arr [.number (String.ofList ['7']), .number (String.ofList ['9']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '8']), .number (String.ofList ['3', '1'])]) :: (acc))

theorem array_fragment0112954_chunk_000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 23) (SourceJson.white (fragment0112954Chunk000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 21) (SourceJson.white tail) (fragment0112954Chunk000Push00 acc) := by
  rfl

noncomputable def fragment0112954Acc00100 : List SourceJson := fragment0112954Chunk000Push00 fragment0112954Acc00000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0112954_array_chunk_000"
  err.flush

noncomputable def fragment0112954Chunk001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0112954Chunk001Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['7']), .number (String.ofList ['9']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '8']), .number (String.ofList ['3', '0']), .number (String.ofList ['3', '1'])]) :: ((.arr [.number (String.ofList ['7']), .number (String.ofList ['9']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6']), .number (String.ofList ['3', '0']), .number (String.ofList ['3', '1'])]) :: (acc))

theorem array_fragment0112954_chunk_001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 21) (SourceJson.white (fragment0112954Chunk001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 19) (SourceJson.white tail) (fragment0112954Chunk001Push00 acc) := by
  rfl

noncomputable def fragment0112954Acc00200 : List SourceJson := fragment0112954Chunk001Push00 fragment0112954Acc00100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0112954_array_chunk_001"
  err.flush

noncomputable def fragment0112954Chunk002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0112954Chunk002Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['7']), .number (String.ofList ['9']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '8']), .number (String.ofList ['3', '0']), .number (String.ofList ['3', '1'])]) :: ((.arr [.number (String.ofList ['7']), .number (String.ofList ['9']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '8']), .number (String.ofList ['3', '0']), .number (String.ofList ['3', '1'])]) :: (acc))

theorem array_fragment0112954_chunk_002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 19) (SourceJson.white (fragment0112954Chunk002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 17) (SourceJson.white tail) (fragment0112954Chunk002Push00 acc) := by
  rfl

noncomputable def fragment0112954Acc00300 : List SourceJson := fragment0112954Chunk002Push00 fragment0112954Acc00200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0112954_array_chunk_002"
  err.flush

noncomputable def fragment0112954Chunk003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0112954Chunk003Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['9']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '8']), .number (String.ofList ['3', '0']), .number (String.ofList ['3', '1'])]) :: ((.arr [.number (String.ofList ['7']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '9'])]) :: (acc))

theorem array_fragment0112954_chunk_003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 17) (SourceJson.white (fragment0112954Chunk003Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 15) (SourceJson.white tail) (fragment0112954Chunk003Push00 acc) := by
  rfl

noncomputable def fragment0112954Acc00400 : List SourceJson := fragment0112954Chunk003Push00 fragment0112954Acc00300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0112954_array_chunk_003"
  err.flush

noncomputable def fragment0112954Chunk004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']']
noncomputable def fragment0112954Chunk004Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '8']), .number (String.ofList ['3', '0']), .number (String.ofList ['3', '1'])]) :: (acc)

theorem array_fragment0112954_chunk_004 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 15) (SourceJson.white (fragment0112954Chunk004Chars00 ++ tail)) acc =
      .ok (.arr ((fragment0112954Chunk004Push00 acc).reverse), tail) := by
  rfl

noncomputable def fragment0112954Acc00500 : List SourceJson := fragment0112954Chunk004Push00 fragment0112954Acc00400

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0112954_array_chunk_004"
  err.flush

noncomputable def fragment0112954Chars : List Char := '[' :: (fragment0112954Chunk000Chars00 ++ fragment0112954Chunk001Chars00 ++ fragment0112954Chunk002Chars00 ++ fragment0112954Chunk003Chars00 ++ fragment0112954Chunk004Chars00)
noncomputable def fragment0112954Value : SourceJson := .arr (fragment0112954Acc00500.reverse)

theorem value_fragment0112954 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 24) (fragment0112954Chars ++ tail) =
      .ok (fragment0112954Value, tail) := by
  have hinput : fragment0112954Chars ++ tail = '[' :: (fragment0112954Chunk000Chars00 ++ (fragment0112954Chunk001Chars00 ++ (fragment0112954Chunk002Chars00 ++ (fragment0112954Chunk003Chars00 ++ (fragment0112954Chunk004Chars00 ++ (tail)))))) := by
    simp only [fragment0112954Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 24) (fragment0112954Chars ++ tail) =
        SourceJson.value (fuel + 24) ('[' :: (fragment0112954Chunk000Chars00 ++ (fragment0112954Chunk001Chars00 ++ (fragment0112954Chunk002Chars00 ++ (fragment0112954Chunk003Chars00 ++ (fragment0112954Chunk004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 24)) hinput
    _ = SourceJson.array (fuel + 23) (SourceJson.white (fragment0112954Chunk000Chars00 ++ (fragment0112954Chunk001Chars00 ++ (fragment0112954Chunk002Chars00 ++ (fragment0112954Chunk003Chars00 ++ (fragment0112954Chunk004Chars00 ++ (tail))))))) fragment0112954Acc00000 := by rfl
    _ = SourceJson.array (fuel + 21) (SourceJson.white (fragment0112954Chunk001Chars00 ++ (fragment0112954Chunk002Chars00 ++ (fragment0112954Chunk003Chars00 ++ (fragment0112954Chunk004Chars00 ++ (tail)))))) fragment0112954Acc00100 := array_fragment0112954_chunk_000 fuel (fragment0112954Chunk001Chars00 ++ (fragment0112954Chunk002Chars00 ++ (fragment0112954Chunk003Chars00 ++ (fragment0112954Chunk004Chars00 ++ (tail))))) fragment0112954Acc00000
    _ = SourceJson.array (fuel + 19) (SourceJson.white (fragment0112954Chunk002Chars00 ++ (fragment0112954Chunk003Chars00 ++ (fragment0112954Chunk004Chars00 ++ (tail))))) fragment0112954Acc00200 := array_fragment0112954_chunk_001 fuel (fragment0112954Chunk002Chars00 ++ (fragment0112954Chunk003Chars00 ++ (fragment0112954Chunk004Chars00 ++ (tail)))) fragment0112954Acc00100
    _ = SourceJson.array (fuel + 17) (SourceJson.white (fragment0112954Chunk003Chars00 ++ (fragment0112954Chunk004Chars00 ++ (tail)))) fragment0112954Acc00300 := array_fragment0112954_chunk_002 fuel (fragment0112954Chunk003Chars00 ++ (fragment0112954Chunk004Chars00 ++ (tail))) fragment0112954Acc00200
    _ = SourceJson.array (fuel + 15) (SourceJson.white (fragment0112954Chunk004Chars00 ++ (tail))) fragment0112954Acc00400 := array_fragment0112954_chunk_003 fuel (fragment0112954Chunk004Chars00 ++ (tail)) fragment0112954Acc00300
    _ = .ok (fragment0112954Value, tail) := array_fragment0112954_chunk_004 fuel (tail) fragment0112954Acc00400

noncomputable def fragment0112678Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0112678Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0112678Field000Value00 : SourceJson := .arr [.number (String.ofList ['7']), .number (String.ofList ['9']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '8']), .number (String.ofList ['3', '0']), .number (String.ofList ['3', '1'])]
noncomputable def fragment0112678Acc00100 : List (String × SourceJson) := (fragment0112678Field000Key00, fragment0112678Field000Value00) :: fragment0112678Acc00000
noncomputable def fragment0112678Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0112678_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 28) (SourceJson.white (fragment0112678Field000Chars00 ++ tail)) fragment0112678Acc00000 =
      SourceJson.object (fuel + 27) (SourceJson.white tail) fragment0112678Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0112678_object_field_000"
  err.flush

noncomputable def fragment0112678Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0112678Field001Value00 : SourceJson := .number (String.ofList ['7'])
noncomputable def fragment0112678Acc00200 : List (String × SourceJson) := (fragment0112678Field001Key00, fragment0112678Field001Value00) :: fragment0112678Acc00100
noncomputable def fragment0112678Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '7', ',']

theorem object_fragment0112678_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 27) (SourceJson.white (fragment0112678Field001Chars00 ++ tail)) fragment0112678Acc00100 =
      SourceJson.object (fuel + 26) (SourceJson.white tail) fragment0112678Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0112678_object_field_001"
  err.flush

noncomputable def fragment0112678Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0112678Field002Value00 : SourceJson := .number (String.ofList ['3', '1'])
noncomputable def fragment0112678Acc00300 : List (String × SourceJson) := (fragment0112678Field002Key00, fragment0112678Field002Value00) :: fragment0112678Acc00200
noncomputable def fragment0112678Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '3', '1', ',']

theorem object_fragment0112678_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 26) (SourceJson.white (fragment0112678Field002Chars00 ++ tail)) fragment0112678Acc00200 =
      SourceJson.object (fuel + 25) (SourceJson.white tail) fragment0112678Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0112678_object_field_002"
  err.flush

noncomputable def fragment0112678Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0112678Field003Value00 : SourceJson := fragment0112954Value
noncomputable def fragment0112678Acc00400 : List (String × SourceJson) := (fragment0112678Field003Key00, fragment0112678Field003Value00) :: fragment0112678Acc00300
noncomputable def fragment0112678Field003HeaderChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ']
noncomputable def fragment0112678Field003SuffixChars00 : List Char := [',']
noncomputable def fragment0112678Field003Chars00 : List Char := fragment0112678Field003HeaderChars00 ++ fragment0112954Chars ++ fragment0112678Field003SuffixChars00

noncomputable def fragment0112678Field003AfterValue00 (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending => .ok (.obj (((fragment0112678Field003Key00, result.1) :: fragment0112678Acc00300).reverse), ending)
  | ',' :: ending => SourceJson.object fuel (SourceJson.white ending) ((fragment0112678Field003Key00, result.1) :: fragment0112678Acc00300)
  | _ => .error "object separator missing"

theorem object_fragment0112678_field_003_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 25) (SourceJson.white (fragment0112678Field003HeaderChars00 ++ rest)) fragment0112678Acc00300 =
      (SourceJson.value (fuel + 24) rest).bind (fragment0112678Field003AfterValue00 (fuel + 24)) := by rfl

theorem object_fragment0112678_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 25) (SourceJson.white (fragment0112678Field003Chars00 ++ tail)) fragment0112678Acc00300 =
      SourceJson.object (fuel + 24) (SourceJson.white tail) fragment0112678Acc00400 := by
  have hinput : fragment0112678Field003Chars00 ++ tail = fragment0112678Field003HeaderChars00 ++ (fragment0112954Chars ++ (fragment0112678Field003SuffixChars00 ++ tail)) := by
    simp only [fragment0112678Field003Chars00, List.append_assoc]
  calc
    SourceJson.object (fuel + 25) (SourceJson.white (fragment0112678Field003Chars00 ++ tail)) fragment0112678Acc00300 =
        SourceJson.object (fuel + 25)
          (SourceJson.white (fragment0112678Field003HeaderChars00 ++ (fragment0112954Chars ++ (fragment0112678Field003SuffixChars00 ++ tail)))) fragment0112678Acc00300 :=
      congrArg (fun s => SourceJson.object (fuel + 25) (SourceJson.white s) fragment0112678Acc00300) hinput
    _ = (SourceJson.value (fuel + 24) (fragment0112954Chars ++ (fragment0112678Field003SuffixChars00 ++ tail))).bind
        (fragment0112678Field003AfterValue00 (fuel + 24)) := object_fragment0112678_field_003_header fuel (fragment0112954Chars ++ (fragment0112678Field003SuffixChars00 ++ tail))
    _ = (Except.ok (fragment0112954Value, fragment0112678Field003SuffixChars00 ++ tail)).bind (fragment0112678Field003AfterValue00 (fuel + 24)) :=
      congrArg (fun result => result.bind (fragment0112678Field003AfterValue00 (fuel + 24)))
        (value_fragment0112954 (fuel + 0) (fragment0112678Field003SuffixChars00 ++ tail))
    _ = SourceJson.object (fuel + 24) (SourceJson.white tail) fragment0112678Acc00400 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0112678_object_field_003"
  err.flush

noncomputable def fragment0112678Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0112678Field004Value00 : SourceJson := .number (String.ofList ['7'])
noncomputable def fragment0112678Acc00500 : List (String × SourceJson) := (fragment0112678Field004Key00, fragment0112678Field004Value00) :: fragment0112678Acc00400
noncomputable def fragment0112678Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '7', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0112678_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 24) (SourceJson.white (fragment0112678Field004Chars00 ++ tail)) fragment0112678Acc00400 =
      .ok (.obj (fragment0112678Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0112678_object_field_004"
  err.flush

noncomputable def fragment0112678Chars : List Char := '{' :: (fragment0112678Field000Chars00 ++ fragment0112678Field001Chars00 ++ fragment0112678Field002Chars00 ++ fragment0112678Field003Chars00 ++ fragment0112678Field004Chars00)
noncomputable def fragment0112678Value : SourceJson := .obj (fragment0112678Acc00500.reverse)

theorem value_fragment0112678 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 29) (fragment0112678Chars ++ tail) =
      .ok (fragment0112678Value, tail) := by
  have hinput : fragment0112678Chars ++ tail = '{' :: (fragment0112678Field000Chars00 ++ (fragment0112678Field001Chars00 ++ (fragment0112678Field002Chars00 ++ (fragment0112678Field003Chars00 ++ (fragment0112678Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0112678Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 29) (fragment0112678Chars ++ tail) =
        SourceJson.value (fuel + 29) ('{' :: (fragment0112678Field000Chars00 ++ (fragment0112678Field001Chars00 ++ (fragment0112678Field002Chars00 ++ (fragment0112678Field003Chars00 ++ (fragment0112678Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 29)) hinput
    _ = SourceJson.object (fuel + 28) (SourceJson.white (fragment0112678Field000Chars00 ++ (fragment0112678Field001Chars00 ++ (fragment0112678Field002Chars00 ++ (fragment0112678Field003Chars00 ++ (fragment0112678Field004Chars00 ++ (tail))))))) fragment0112678Acc00000 := by rfl
    _ = SourceJson.object (fuel + 27) (SourceJson.white (fragment0112678Field001Chars00 ++ (fragment0112678Field002Chars00 ++ (fragment0112678Field003Chars00 ++ (fragment0112678Field004Chars00 ++ (tail)))))) fragment0112678Acc00100 := object_fragment0112678_field_000 fuel (fragment0112678Field001Chars00 ++ (fragment0112678Field002Chars00 ++ (fragment0112678Field003Chars00 ++ (fragment0112678Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 26) (SourceJson.white (fragment0112678Field002Chars00 ++ (fragment0112678Field003Chars00 ++ (fragment0112678Field004Chars00 ++ (tail))))) fragment0112678Acc00200 := object_fragment0112678_field_001 fuel (fragment0112678Field002Chars00 ++ (fragment0112678Field003Chars00 ++ (fragment0112678Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 25) (SourceJson.white (fragment0112678Field003Chars00 ++ (fragment0112678Field004Chars00 ++ (tail)))) fragment0112678Acc00300 := object_fragment0112678_field_002 fuel (fragment0112678Field003Chars00 ++ (fragment0112678Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 24) (SourceJson.white (fragment0112678Field004Chars00 ++ (tail))) fragment0112678Acc00400 := object_fragment0112678_field_003 fuel (fragment0112678Field004Chars00 ++ (tail))
    _ = .ok (fragment0112678Value, tail) := object_fragment0112678_field_004 fuel (tail)

noncomputable def fragment0114904Acc00000 : List SourceJson := []

noncomputable def fragment0114904Chunk000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0114904Chunk000Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['7']), .number (String.ofList ['9']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6']), .number (String.ofList ['3', '0'])]) :: ((.arr [.number (String.ofList ['7']), .number (String.ofList ['9']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '6']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '8'])]) :: (acc))

theorem array_fragment0114904_chunk_000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 20) (SourceJson.white (fragment0114904Chunk000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 18) (SourceJson.white tail) (fragment0114904Chunk000Push00 acc) := by
  rfl

noncomputable def fragment0114904Acc00100 : List SourceJson := fragment0114904Chunk000Push00 fragment0114904Acc00000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0114904_array_chunk_000"
  err.flush

noncomputable def fragment0114904Chunk001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0114904Chunk001Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['7']), .number (String.ofList ['9']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '8']), .number (String.ofList ['3', '0'])]) :: ((.arr [.number (String.ofList ['7']), .number (String.ofList ['9']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '8']), .number (String.ofList ['3', '0'])]) :: (acc))

theorem array_fragment0114904_chunk_001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 18) (SourceJson.white (fragment0114904Chunk001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 16) (SourceJson.white tail) (fragment0114904Chunk001Push00 acc) := by
  rfl

noncomputable def fragment0114904Acc00200 : List SourceJson := fragment0114904Chunk001Push00 fragment0114904Acc00100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0114904_array_chunk_001"
  err.flush

noncomputable def fragment0114904Chunk002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0114904Chunk002Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['7']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '9'])]) :: ((.arr [.number (String.ofList ['7']), .number (String.ofList ['9']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '8']), .number (String.ofList ['3', '0'])]) :: (acc))

theorem array_fragment0114904_chunk_002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 16) (SourceJson.white (fragment0114904Chunk002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 14) (SourceJson.white tail) (fragment0114904Chunk002Push00 acc) := by
  rfl

noncomputable def fragment0114904Acc00300 : List SourceJson := fragment0114904Chunk002Push00 fragment0114904Acc00200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0114904_array_chunk_002"
  err.flush

noncomputable def fragment0114904Chunk003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']']
noncomputable def fragment0114904Chunk003Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '8']), .number (String.ofList ['3', '0'])]) :: ((.arr [.number (String.ofList ['9']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '8']), .number (String.ofList ['3', '0'])]) :: (acc))

theorem array_fragment0114904_chunk_003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 14) (SourceJson.white (fragment0114904Chunk003Chars00 ++ tail)) acc =
      .ok (.arr ((fragment0114904Chunk003Push00 acc).reverse), tail) := by
  rfl

noncomputable def fragment0114904Acc00400 : List SourceJson := fragment0114904Chunk003Push00 fragment0114904Acc00300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0114904_array_chunk_003"
  err.flush

noncomputable def fragment0114904Chars : List Char := '[' :: (fragment0114904Chunk000Chars00 ++ fragment0114904Chunk001Chars00 ++ fragment0114904Chunk002Chars00 ++ fragment0114904Chunk003Chars00)
noncomputable def fragment0114904Value : SourceJson := .arr (fragment0114904Acc00400.reverse)

theorem value_fragment0114904 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 21) (fragment0114904Chars ++ tail) =
      .ok (fragment0114904Value, tail) := by
  have hinput : fragment0114904Chars ++ tail = '[' :: (fragment0114904Chunk000Chars00 ++ (fragment0114904Chunk001Chars00 ++ (fragment0114904Chunk002Chars00 ++ (fragment0114904Chunk003Chars00 ++ (tail))))) := by
    simp only [fragment0114904Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 21) (fragment0114904Chars ++ tail) =
        SourceJson.value (fuel + 21) ('[' :: (fragment0114904Chunk000Chars00 ++ (fragment0114904Chunk001Chars00 ++ (fragment0114904Chunk002Chars00 ++ (fragment0114904Chunk003Chars00 ++ (tail)))))) :=
      congrArg (SourceJson.value (fuel + 21)) hinput
    _ = SourceJson.array (fuel + 20) (SourceJson.white (fragment0114904Chunk000Chars00 ++ (fragment0114904Chunk001Chars00 ++ (fragment0114904Chunk002Chars00 ++ (fragment0114904Chunk003Chars00 ++ (tail)))))) fragment0114904Acc00000 := by rfl
    _ = SourceJson.array (fuel + 18) (SourceJson.white (fragment0114904Chunk001Chars00 ++ (fragment0114904Chunk002Chars00 ++ (fragment0114904Chunk003Chars00 ++ (tail))))) fragment0114904Acc00100 := array_fragment0114904_chunk_000 fuel (fragment0114904Chunk001Chars00 ++ (fragment0114904Chunk002Chars00 ++ (fragment0114904Chunk003Chars00 ++ (tail)))) fragment0114904Acc00000
    _ = SourceJson.array (fuel + 16) (SourceJson.white (fragment0114904Chunk002Chars00 ++ (fragment0114904Chunk003Chars00 ++ (tail)))) fragment0114904Acc00200 := array_fragment0114904_chunk_001 fuel (fragment0114904Chunk002Chars00 ++ (fragment0114904Chunk003Chars00 ++ (tail))) fragment0114904Acc00100
    _ = SourceJson.array (fuel + 14) (SourceJson.white (fragment0114904Chunk003Chars00 ++ (tail))) fragment0114904Acc00300 := array_fragment0114904_chunk_002 fuel (fragment0114904Chunk003Chars00 ++ (tail)) fragment0114904Acc00200
    _ = .ok (fragment0114904Value, tail) := array_fragment0114904_chunk_003 fuel (tail) fragment0114904Acc00300

noncomputable def fragment0114654Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0114654Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0114654Field000Value00 : SourceJson := .arr [.number (String.ofList ['7']), .number (String.ofList ['9']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '8']), .number (String.ofList ['3', '0'])]
noncomputable def fragment0114654Acc00100 : List (String × SourceJson) := (fragment0114654Field000Key00, fragment0114654Field000Value00) :: fragment0114654Acc00000
noncomputable def fragment0114654Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0114654_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 25) (SourceJson.white (fragment0114654Field000Chars00 ++ tail)) fragment0114654Acc00000 =
      SourceJson.object (fuel + 24) (SourceJson.white tail) fragment0114654Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0114654_object_field_000"
  err.flush

noncomputable def fragment0114654Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0114654Field001Value00 : SourceJson := .number (String.ofList ['6'])
noncomputable def fragment0114654Acc00200 : List (String × SourceJson) := (fragment0114654Field001Key00, fragment0114654Field001Value00) :: fragment0114654Acc00100
noncomputable def fragment0114654Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '6', ',']

theorem object_fragment0114654_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 24) (SourceJson.white (fragment0114654Field001Chars00 ++ tail)) fragment0114654Acc00100 =
      SourceJson.object (fuel + 23) (SourceJson.white tail) fragment0114654Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0114654_object_field_001"
  err.flush

noncomputable def fragment0114654Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0114654Field002Value00 : SourceJson := .number (String.ofList ['3', '0'])
noncomputable def fragment0114654Acc00300 : List (String × SourceJson) := (fragment0114654Field002Key00, fragment0114654Field002Value00) :: fragment0114654Acc00200
noncomputable def fragment0114654Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '3', '0', ',']

theorem object_fragment0114654_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 23) (SourceJson.white (fragment0114654Field002Chars00 ++ tail)) fragment0114654Acc00200 =
      SourceJson.object (fuel + 22) (SourceJson.white tail) fragment0114654Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0114654_object_field_002"
  err.flush

noncomputable def fragment0114654Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0114654Field003Value00 : SourceJson := fragment0114904Value
noncomputable def fragment0114654Acc00400 : List (String × SourceJson) := (fragment0114654Field003Key00, fragment0114654Field003Value00) :: fragment0114654Acc00300
noncomputable def fragment0114654Field003HeaderChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ']
noncomputable def fragment0114654Field003SuffixChars00 : List Char := [',']
noncomputable def fragment0114654Field003Chars00 : List Char := fragment0114654Field003HeaderChars00 ++ fragment0114904Chars ++ fragment0114654Field003SuffixChars00

noncomputable def fragment0114654Field003AfterValue00 (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending => .ok (.obj (((fragment0114654Field003Key00, result.1) :: fragment0114654Acc00300).reverse), ending)
  | ',' :: ending => SourceJson.object fuel (SourceJson.white ending) ((fragment0114654Field003Key00, result.1) :: fragment0114654Acc00300)
  | _ => .error "object separator missing"

theorem object_fragment0114654_field_003_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 22) (SourceJson.white (fragment0114654Field003HeaderChars00 ++ rest)) fragment0114654Acc00300 =
      (SourceJson.value (fuel + 21) rest).bind (fragment0114654Field003AfterValue00 (fuel + 21)) := by rfl

theorem object_fragment0114654_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 22) (SourceJson.white (fragment0114654Field003Chars00 ++ tail)) fragment0114654Acc00300 =
      SourceJson.object (fuel + 21) (SourceJson.white tail) fragment0114654Acc00400 := by
  have hinput : fragment0114654Field003Chars00 ++ tail = fragment0114654Field003HeaderChars00 ++ (fragment0114904Chars ++ (fragment0114654Field003SuffixChars00 ++ tail)) := by
    simp only [fragment0114654Field003Chars00, List.append_assoc]
  calc
    SourceJson.object (fuel + 22) (SourceJson.white (fragment0114654Field003Chars00 ++ tail)) fragment0114654Acc00300 =
        SourceJson.object (fuel + 22)
          (SourceJson.white (fragment0114654Field003HeaderChars00 ++ (fragment0114904Chars ++ (fragment0114654Field003SuffixChars00 ++ tail)))) fragment0114654Acc00300 :=
      congrArg (fun s => SourceJson.object (fuel + 22) (SourceJson.white s) fragment0114654Acc00300) hinput
    _ = (SourceJson.value (fuel + 21) (fragment0114904Chars ++ (fragment0114654Field003SuffixChars00 ++ tail))).bind
        (fragment0114654Field003AfterValue00 (fuel + 21)) := object_fragment0114654_field_003_header fuel (fragment0114904Chars ++ (fragment0114654Field003SuffixChars00 ++ tail))
    _ = (Except.ok (fragment0114904Value, fragment0114654Field003SuffixChars00 ++ tail)).bind (fragment0114654Field003AfterValue00 (fuel + 21)) :=
      congrArg (fun result => result.bind (fragment0114654Field003AfterValue00 (fuel + 21)))
        (value_fragment0114904 (fuel + 0) (fragment0114654Field003SuffixChars00 ++ tail))
    _ = SourceJson.object (fuel + 21) (SourceJson.white tail) fragment0114654Acc00400 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0114654_object_field_003"
  err.flush

noncomputable def fragment0114654Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0114654Field004Value00 : SourceJson := .number (String.ofList ['6'])
noncomputable def fragment0114654Acc00500 : List (String × SourceJson) := (fragment0114654Field004Key00, fragment0114654Field004Value00) :: fragment0114654Acc00400
noncomputable def fragment0114654Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '6', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0114654_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 21) (SourceJson.white (fragment0114654Field004Chars00 ++ tail)) fragment0114654Acc00400 =
      .ok (.obj (fragment0114654Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0114654_object_field_004"
  err.flush

noncomputable def fragment0114654Chars : List Char := '{' :: (fragment0114654Field000Chars00 ++ fragment0114654Field001Chars00 ++ fragment0114654Field002Chars00 ++ fragment0114654Field003Chars00 ++ fragment0114654Field004Chars00)
noncomputable def fragment0114654Value : SourceJson := .obj (fragment0114654Acc00500.reverse)

theorem value_fragment0114654 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 26) (fragment0114654Chars ++ tail) =
      .ok (fragment0114654Value, tail) := by
  have hinput : fragment0114654Chars ++ tail = '{' :: (fragment0114654Field000Chars00 ++ (fragment0114654Field001Chars00 ++ (fragment0114654Field002Chars00 ++ (fragment0114654Field003Chars00 ++ (fragment0114654Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0114654Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 26) (fragment0114654Chars ++ tail) =
        SourceJson.value (fuel + 26) ('{' :: (fragment0114654Field000Chars00 ++ (fragment0114654Field001Chars00 ++ (fragment0114654Field002Chars00 ++ (fragment0114654Field003Chars00 ++ (fragment0114654Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 26)) hinput
    _ = SourceJson.object (fuel + 25) (SourceJson.white (fragment0114654Field000Chars00 ++ (fragment0114654Field001Chars00 ++ (fragment0114654Field002Chars00 ++ (fragment0114654Field003Chars00 ++ (fragment0114654Field004Chars00 ++ (tail))))))) fragment0114654Acc00000 := by rfl
    _ = SourceJson.object (fuel + 24) (SourceJson.white (fragment0114654Field001Chars00 ++ (fragment0114654Field002Chars00 ++ (fragment0114654Field003Chars00 ++ (fragment0114654Field004Chars00 ++ (tail)))))) fragment0114654Acc00100 := object_fragment0114654_field_000 fuel (fragment0114654Field001Chars00 ++ (fragment0114654Field002Chars00 ++ (fragment0114654Field003Chars00 ++ (fragment0114654Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 23) (SourceJson.white (fragment0114654Field002Chars00 ++ (fragment0114654Field003Chars00 ++ (fragment0114654Field004Chars00 ++ (tail))))) fragment0114654Acc00200 := object_fragment0114654_field_001 fuel (fragment0114654Field002Chars00 ++ (fragment0114654Field003Chars00 ++ (fragment0114654Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 22) (SourceJson.white (fragment0114654Field003Chars00 ++ (fragment0114654Field004Chars00 ++ (tail)))) fragment0114654Acc00300 := object_fragment0114654_field_002 fuel (fragment0114654Field003Chars00 ++ (fragment0114654Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 21) (SourceJson.white (fragment0114654Field004Chars00 ++ (tail))) fragment0114654Acc00400 := object_fragment0114654_field_003 fuel (fragment0114654Field004Chars00 ++ (tail))
    _ = .ok (fragment0114654Value, tail) := object_fragment0114654_field_004 fuel (tail)

noncomputable def fragment0116418Acc00000 : List SourceJson := []

noncomputable def fragment0116418Chunk000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0116418Chunk000Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['7']), .number (String.ofList ['9']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '6']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '8'])]) :: ((.arr [.number (String.ofList ['7']), .number (String.ofList ['9']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '4']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6'])]) :: (acc))

theorem array_fragment0116418_chunk_000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 17) (SourceJson.white (fragment0116418Chunk000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 15) (SourceJson.white tail) (fragment0116418Chunk000Push00 acc) := by
  rfl

noncomputable def fragment0116418Acc00100 : List SourceJson := fragment0116418Chunk000Push00 fragment0116418Acc00000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0116418_array_chunk_000"
  err.flush

noncomputable def fragment0116418Chunk001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0116418Chunk001Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['7']), .number (String.ofList ['9']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '6']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '8'])]) :: ((.arr [.number (String.ofList ['7']), .number (String.ofList ['9']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '6']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '8'])]) :: (acc))

theorem array_fragment0116418_chunk_001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 15) (SourceJson.white (fragment0116418Chunk001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 13) (SourceJson.white tail) (fragment0116418Chunk001Push00 acc) := by
  rfl

noncomputable def fragment0116418Acc00200 : List SourceJson := fragment0116418Chunk001Push00 fragment0116418Acc00100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0116418_array_chunk_001"
  err.flush

noncomputable def fragment0116418Chunk002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0116418Chunk002Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['9']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '8'])]) :: ((.arr [.number (String.ofList ['7']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '6'])]) :: (acc))

theorem array_fragment0116418_chunk_002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 13) (SourceJson.white (fragment0116418Chunk002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 11) (SourceJson.white tail) (fragment0116418Chunk002Push00 acc) := by
  rfl

noncomputable def fragment0116418Acc00300 : List SourceJson := fragment0116418Chunk002Push00 fragment0116418Acc00200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0116418_array_chunk_002"
  err.flush

noncomputable def fragment0116418Chunk003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']']
noncomputable def fragment0116418Chunk003Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '6']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '8'])]) :: (acc)

theorem array_fragment0116418_chunk_003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 11) (SourceJson.white (fragment0116418Chunk003Chars00 ++ tail)) acc =
      .ok (.arr ((fragment0116418Chunk003Push00 acc).reverse), tail) := by
  rfl

noncomputable def fragment0116418Acc00400 : List SourceJson := fragment0116418Chunk003Push00 fragment0116418Acc00300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0116418_array_chunk_003"
  err.flush

noncomputable def fragment0116418Chars : List Char := '[' :: (fragment0116418Chunk000Chars00 ++ fragment0116418Chunk001Chars00 ++ fragment0116418Chunk002Chars00 ++ fragment0116418Chunk003Chars00)
noncomputable def fragment0116418Value : SourceJson := .arr (fragment0116418Acc00400.reverse)

theorem value_fragment0116418 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 18) (fragment0116418Chars ++ tail) =
      .ok (fragment0116418Value, tail) := by
  have hinput : fragment0116418Chars ++ tail = '[' :: (fragment0116418Chunk000Chars00 ++ (fragment0116418Chunk001Chars00 ++ (fragment0116418Chunk002Chars00 ++ (fragment0116418Chunk003Chars00 ++ (tail))))) := by
    simp only [fragment0116418Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 18) (fragment0116418Chars ++ tail) =
        SourceJson.value (fuel + 18) ('[' :: (fragment0116418Chunk000Chars00 ++ (fragment0116418Chunk001Chars00 ++ (fragment0116418Chunk002Chars00 ++ (fragment0116418Chunk003Chars00 ++ (tail)))))) :=
      congrArg (SourceJson.value (fuel + 18)) hinput
    _ = SourceJson.array (fuel + 17) (SourceJson.white (fragment0116418Chunk000Chars00 ++ (fragment0116418Chunk001Chars00 ++ (fragment0116418Chunk002Chars00 ++ (fragment0116418Chunk003Chars00 ++ (tail)))))) fragment0116418Acc00000 := by rfl
    _ = SourceJson.array (fuel + 15) (SourceJson.white (fragment0116418Chunk001Chars00 ++ (fragment0116418Chunk002Chars00 ++ (fragment0116418Chunk003Chars00 ++ (tail))))) fragment0116418Acc00100 := array_fragment0116418_chunk_000 fuel (fragment0116418Chunk001Chars00 ++ (fragment0116418Chunk002Chars00 ++ (fragment0116418Chunk003Chars00 ++ (tail)))) fragment0116418Acc00000
    _ = SourceJson.array (fuel + 13) (SourceJson.white (fragment0116418Chunk002Chars00 ++ (fragment0116418Chunk003Chars00 ++ (tail)))) fragment0116418Acc00200 := array_fragment0116418_chunk_001 fuel (fragment0116418Chunk002Chars00 ++ (fragment0116418Chunk003Chars00 ++ (tail))) fragment0116418Acc00100
    _ = SourceJson.array (fuel + 11) (SourceJson.white (fragment0116418Chunk003Chars00 ++ (tail))) fragment0116418Acc00300 := array_fragment0116418_chunk_002 fuel (fragment0116418Chunk003Chars00 ++ (tail)) fragment0116418Acc00200
    _ = .ok (fragment0116418Value, tail) := array_fragment0116418_chunk_003 fuel (tail) fragment0116418Acc00300

noncomputable def fragment0116194Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0116194Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0116194Field000Value00 : SourceJson := .arr [.number (String.ofList ['7']), .number (String.ofList ['9']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '6']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '8'])]
noncomputable def fragment0116194Acc00100 : List (String × SourceJson) := (fragment0116194Field000Key00, fragment0116194Field000Value00) :: fragment0116194Acc00000
noncomputable def fragment0116194Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0116194_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 22) (SourceJson.white (fragment0116194Field000Chars00 ++ tail)) fragment0116194Acc00000 =
      SourceJson.object (fuel + 21) (SourceJson.white tail) fragment0116194Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0116194_object_field_000"
  err.flush

noncomputable def fragment0116194Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0116194Field001Value00 : SourceJson := .number (String.ofList ['5'])
noncomputable def fragment0116194Acc00200 : List (String × SourceJson) := (fragment0116194Field001Key00, fragment0116194Field001Value00) :: fragment0116194Acc00100
noncomputable def fragment0116194Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '5', ',']

theorem object_fragment0116194_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 21) (SourceJson.white (fragment0116194Field001Chars00 ++ tail)) fragment0116194Acc00100 =
      SourceJson.object (fuel + 20) (SourceJson.white tail) fragment0116194Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0116194_object_field_001"
  err.flush

noncomputable def fragment0116194Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0116194Field002Value00 : SourceJson := .number (String.ofList ['2', '8'])
noncomputable def fragment0116194Acc00300 : List (String × SourceJson) := (fragment0116194Field002Key00, fragment0116194Field002Value00) :: fragment0116194Acc00200
noncomputable def fragment0116194Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '2', '8', ',']

theorem object_fragment0116194_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 20) (SourceJson.white (fragment0116194Field002Chars00 ++ tail)) fragment0116194Acc00200 =
      SourceJson.object (fuel + 19) (SourceJson.white tail) fragment0116194Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0116194_object_field_002"
  err.flush

noncomputable def fragment0116194Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0116194Field003Value00 : SourceJson := fragment0116418Value
noncomputable def fragment0116194Acc00400 : List (String × SourceJson) := (fragment0116194Field003Key00, fragment0116194Field003Value00) :: fragment0116194Acc00300
noncomputable def fragment0116194Field003HeaderChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ']
noncomputable def fragment0116194Field003SuffixChars00 : List Char := [',']
noncomputable def fragment0116194Field003Chars00 : List Char := fragment0116194Field003HeaderChars00 ++ fragment0116418Chars ++ fragment0116194Field003SuffixChars00

noncomputable def fragment0116194Field003AfterValue00 (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending => .ok (.obj (((fragment0116194Field003Key00, result.1) :: fragment0116194Acc00300).reverse), ending)
  | ',' :: ending => SourceJson.object fuel (SourceJson.white ending) ((fragment0116194Field003Key00, result.1) :: fragment0116194Acc00300)
  | _ => .error "object separator missing"

theorem object_fragment0116194_field_003_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 19) (SourceJson.white (fragment0116194Field003HeaderChars00 ++ rest)) fragment0116194Acc00300 =
      (SourceJson.value (fuel + 18) rest).bind (fragment0116194Field003AfterValue00 (fuel + 18)) := by rfl

theorem object_fragment0116194_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 19) (SourceJson.white (fragment0116194Field003Chars00 ++ tail)) fragment0116194Acc00300 =
      SourceJson.object (fuel + 18) (SourceJson.white tail) fragment0116194Acc00400 := by
  have hinput : fragment0116194Field003Chars00 ++ tail = fragment0116194Field003HeaderChars00 ++ (fragment0116418Chars ++ (fragment0116194Field003SuffixChars00 ++ tail)) := by
    simp only [fragment0116194Field003Chars00, List.append_assoc]
  calc
    SourceJson.object (fuel + 19) (SourceJson.white (fragment0116194Field003Chars00 ++ tail)) fragment0116194Acc00300 =
        SourceJson.object (fuel + 19)
          (SourceJson.white (fragment0116194Field003HeaderChars00 ++ (fragment0116418Chars ++ (fragment0116194Field003SuffixChars00 ++ tail)))) fragment0116194Acc00300 :=
      congrArg (fun s => SourceJson.object (fuel + 19) (SourceJson.white s) fragment0116194Acc00300) hinput
    _ = (SourceJson.value (fuel + 18) (fragment0116418Chars ++ (fragment0116194Field003SuffixChars00 ++ tail))).bind
        (fragment0116194Field003AfterValue00 (fuel + 18)) := object_fragment0116194_field_003_header fuel (fragment0116418Chars ++ (fragment0116194Field003SuffixChars00 ++ tail))
    _ = (Except.ok (fragment0116418Value, fragment0116194Field003SuffixChars00 ++ tail)).bind (fragment0116194Field003AfterValue00 (fuel + 18)) :=
      congrArg (fun result => result.bind (fragment0116194Field003AfterValue00 (fuel + 18)))
        (value_fragment0116418 (fuel + 0) (fragment0116194Field003SuffixChars00 ++ tail))
    _ = SourceJson.object (fuel + 18) (SourceJson.white tail) fragment0116194Acc00400 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0116194_object_field_003"
  err.flush

noncomputable def fragment0116194Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0116194Field004Value00 : SourceJson := .number (String.ofList ['5'])
noncomputable def fragment0116194Acc00500 : List (String × SourceJson) := (fragment0116194Field004Key00, fragment0116194Field004Value00) :: fragment0116194Acc00400
noncomputable def fragment0116194Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '5', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0116194_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 18) (SourceJson.white (fragment0116194Field004Chars00 ++ tail)) fragment0116194Acc00400 =
      .ok (.obj (fragment0116194Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0116194_object_field_004"
  err.flush

noncomputable def fragment0116194Chars : List Char := '{' :: (fragment0116194Field000Chars00 ++ fragment0116194Field001Chars00 ++ fragment0116194Field002Chars00 ++ fragment0116194Field003Chars00 ++ fragment0116194Field004Chars00)
noncomputable def fragment0116194Value : SourceJson := .obj (fragment0116194Acc00500.reverse)

theorem value_fragment0116194 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 23) (fragment0116194Chars ++ tail) =
      .ok (fragment0116194Value, tail) := by
  have hinput : fragment0116194Chars ++ tail = '{' :: (fragment0116194Field000Chars00 ++ (fragment0116194Field001Chars00 ++ (fragment0116194Field002Chars00 ++ (fragment0116194Field003Chars00 ++ (fragment0116194Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0116194Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 23) (fragment0116194Chars ++ tail) =
        SourceJson.value (fuel + 23) ('{' :: (fragment0116194Field000Chars00 ++ (fragment0116194Field001Chars00 ++ (fragment0116194Field002Chars00 ++ (fragment0116194Field003Chars00 ++ (fragment0116194Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 23)) hinput
    _ = SourceJson.object (fuel + 22) (SourceJson.white (fragment0116194Field000Chars00 ++ (fragment0116194Field001Chars00 ++ (fragment0116194Field002Chars00 ++ (fragment0116194Field003Chars00 ++ (fragment0116194Field004Chars00 ++ (tail))))))) fragment0116194Acc00000 := by rfl
    _ = SourceJson.object (fuel + 21) (SourceJson.white (fragment0116194Field001Chars00 ++ (fragment0116194Field002Chars00 ++ (fragment0116194Field003Chars00 ++ (fragment0116194Field004Chars00 ++ (tail)))))) fragment0116194Acc00100 := object_fragment0116194_field_000 fuel (fragment0116194Field001Chars00 ++ (fragment0116194Field002Chars00 ++ (fragment0116194Field003Chars00 ++ (fragment0116194Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 20) (SourceJson.white (fragment0116194Field002Chars00 ++ (fragment0116194Field003Chars00 ++ (fragment0116194Field004Chars00 ++ (tail))))) fragment0116194Acc00200 := object_fragment0116194_field_001 fuel (fragment0116194Field002Chars00 ++ (fragment0116194Field003Chars00 ++ (fragment0116194Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 19) (SourceJson.white (fragment0116194Field003Chars00 ++ (fragment0116194Field004Chars00 ++ (tail)))) fragment0116194Acc00300 := object_fragment0116194_field_002 fuel (fragment0116194Field003Chars00 ++ (fragment0116194Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 18) (SourceJson.white (fragment0116194Field004Chars00 ++ (tail))) fragment0116194Acc00400 := object_fragment0116194_field_003 fuel (fragment0116194Field004Chars00 ++ (tail))
    _ = .ok (fragment0116194Value, tail) := object_fragment0116194_field_004 fuel (tail)

noncomputable def fragment0117358Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0117358Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0117358Field000Value00 : SourceJson := .arr [.number (String.ofList ['7']), .number (String.ofList ['9']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '4']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6'])]
noncomputable def fragment0117358Acc00100 : List (String × SourceJson) := (fragment0117358Field000Key00, fragment0117358Field000Value00) :: fragment0117358Acc00000
noncomputable def fragment0117358Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0117358_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 19) (SourceJson.white (fragment0117358Field000Chars00 ++ tail)) fragment0117358Acc00000 =
      SourceJson.object (fuel + 18) (SourceJson.white tail) fragment0117358Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0117358_object_field_000"
  err.flush

noncomputable def fragment0117358Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0117358Field001Value00 : SourceJson := .number (String.ofList ['4'])
noncomputable def fragment0117358Acc00200 : List (String × SourceJson) := (fragment0117358Field001Key00, fragment0117358Field001Value00) :: fragment0117358Acc00100
noncomputable def fragment0117358Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '4', ',']

theorem object_fragment0117358_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 18) (SourceJson.white (fragment0117358Field001Chars00 ++ tail)) fragment0117358Acc00100 =
      SourceJson.object (fuel + 17) (SourceJson.white tail) fragment0117358Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0117358_object_field_001"
  err.flush

noncomputable def fragment0117358Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0117358Field002Value00 : SourceJson := .number (String.ofList ['2', '6'])
noncomputable def fragment0117358Acc00300 : List (String × SourceJson) := (fragment0117358Field002Key00, fragment0117358Field002Value00) :: fragment0117358Acc00200
noncomputable def fragment0117358Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '2', '6', ',']

theorem object_fragment0117358_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 17) (SourceJson.white (fragment0117358Field002Chars00 ++ tail)) fragment0117358Acc00200 =
      SourceJson.object (fuel + 16) (SourceJson.white tail) fragment0117358Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0117358_object_field_002"
  err.flush

noncomputable def fragment0117358Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0117358Field003Value00 : SourceJson := .arr [.arr [.number (String.ofList ['7']), .number (String.ofList ['9']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6'])], .arr [.number (String.ofList ['7']), .number (String.ofList ['9']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '4']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5'])], .arr [.number (String.ofList ['7']), .number (String.ofList ['9']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '4']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '6'])], .arr [.number (String.ofList ['7']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '4'])], .arr [.number (String.ofList ['9']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6'])], .arr [.number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '4']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6'])]]
noncomputable def fragment0117358Acc00400 : List (String × SourceJson) := (fragment0117358Field003Key00, fragment0117358Field003Value00) :: fragment0117358Acc00300
noncomputable def fragment0117358Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0117358_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 16) (SourceJson.white (fragment0117358Field003Chars00 ++ tail)) fragment0117358Acc00300 =
      SourceJson.object (fuel + 15) (SourceJson.white tail) fragment0117358Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0117358_object_field_003"
  err.flush

noncomputable def fragment0117358Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0117358Field004Value00 : SourceJson := .number (String.ofList ['4'])
noncomputable def fragment0117358Acc00500 : List (String × SourceJson) := (fragment0117358Field004Key00, fragment0117358Field004Value00) :: fragment0117358Acc00400
noncomputable def fragment0117358Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0117358_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 15) (SourceJson.white (fragment0117358Field004Chars00 ++ tail)) fragment0117358Acc00400 =
      .ok (.obj (fragment0117358Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0117358_object_field_004"
  err.flush

noncomputable def fragment0117358Chars : List Char := '{' :: (fragment0117358Field000Chars00 ++ fragment0117358Field001Chars00 ++ fragment0117358Field002Chars00 ++ fragment0117358Field003Chars00 ++ fragment0117358Field004Chars00)
noncomputable def fragment0117358Value : SourceJson := .obj (fragment0117358Acc00500.reverse)

theorem value_fragment0117358 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 20) (fragment0117358Chars ++ tail) =
      .ok (fragment0117358Value, tail) := by
  have hinput : fragment0117358Chars ++ tail = '{' :: (fragment0117358Field000Chars00 ++ (fragment0117358Field001Chars00 ++ (fragment0117358Field002Chars00 ++ (fragment0117358Field003Chars00 ++ (fragment0117358Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0117358Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 20) (fragment0117358Chars ++ tail) =
        SourceJson.value (fuel + 20) ('{' :: (fragment0117358Field000Chars00 ++ (fragment0117358Field001Chars00 ++ (fragment0117358Field002Chars00 ++ (fragment0117358Field003Chars00 ++ (fragment0117358Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 20)) hinput
    _ = SourceJson.object (fuel + 19) (SourceJson.white (fragment0117358Field000Chars00 ++ (fragment0117358Field001Chars00 ++ (fragment0117358Field002Chars00 ++ (fragment0117358Field003Chars00 ++ (fragment0117358Field004Chars00 ++ (tail))))))) fragment0117358Acc00000 := by rfl
    _ = SourceJson.object (fuel + 18) (SourceJson.white (fragment0117358Field001Chars00 ++ (fragment0117358Field002Chars00 ++ (fragment0117358Field003Chars00 ++ (fragment0117358Field004Chars00 ++ (tail)))))) fragment0117358Acc00100 := object_fragment0117358_field_000 fuel (fragment0117358Field001Chars00 ++ (fragment0117358Field002Chars00 ++ (fragment0117358Field003Chars00 ++ (fragment0117358Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 17) (SourceJson.white (fragment0117358Field002Chars00 ++ (fragment0117358Field003Chars00 ++ (fragment0117358Field004Chars00 ++ (tail))))) fragment0117358Acc00200 := object_fragment0117358_field_001 fuel (fragment0117358Field002Chars00 ++ (fragment0117358Field003Chars00 ++ (fragment0117358Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 16) (SourceJson.white (fragment0117358Field003Chars00 ++ (fragment0117358Field004Chars00 ++ (tail)))) fragment0117358Acc00300 := object_fragment0117358_field_002 fuel (fragment0117358Field003Chars00 ++ (fragment0117358Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 15) (SourceJson.white (fragment0117358Field004Chars00 ++ (tail))) fragment0117358Acc00400 := object_fragment0117358_field_003 fuel (fragment0117358Field004Chars00 ++ (tail))
    _ = .ok (fragment0117358Value, tail) := object_fragment0117358_field_004 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0040_before_reader"
  err.flush

noncomputable def chunk0040LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0040SuffixChars00 : List Char := [',']
noncomputable def chunk0040Chars00 : List Char := chunk0040LeadChars00 ++ fragment0112678Chars ++ chunk0040SuffixChars00
noncomputable def chunk0040Push00 (acc : List SourceJson) : List SourceJson := fragment0112678Value :: acc

noncomputable def chunk0040AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0040_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 33)
      (SourceJson.white (chunk0040LeadChars00 ++ (fragment0112678Chars ++ rest))) acc =
      (SourceJson.value (fuel + 32) (fragment0112678Chars ++ rest)).bind
        (chunk0040AfterValue00 (fuel + 32) acc) := by rfl

theorem array_chunk0040 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 33) (SourceJson.white (chunk0040Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 32) (SourceJson.white tail) (chunk0040Push00 acc) := by
  have hinput : chunk0040Chars00 ++ tail = chunk0040LeadChars00 ++ (fragment0112678Chars ++ (chunk0040SuffixChars00 ++ tail)) := by
    simp only [chunk0040Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 33) (SourceJson.white (chunk0040Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 33)
          (SourceJson.white (chunk0040LeadChars00 ++ (fragment0112678Chars ++ (chunk0040SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 33) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 32) (fragment0112678Chars ++ (chunk0040SuffixChars00 ++ tail))).bind
        (chunk0040AfterValue00 (fuel + 32) acc) := array_chunk0040_head fuel (chunk0040SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0112678Value, chunk0040SuffixChars00 ++ tail)).bind
        (chunk0040AfterValue00 (fuel + 32) acc) :=
      congrArg (fun result => result.bind (chunk0040AfterValue00 (fuel + 32) acc))
        (value_fragment0112678 (fuel + 3) (chunk0040SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 32) (SourceJson.white tail) (chunk0040Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0040_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0041_before_reader"
  err.flush

noncomputable def chunk0041LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0041SuffixChars00 : List Char := [',']
noncomputable def chunk0041Chars00 : List Char := chunk0041LeadChars00 ++ fragment0114654Chars ++ chunk0041SuffixChars00
noncomputable def chunk0041Push00 (acc : List SourceJson) : List SourceJson := fragment0114654Value :: acc

noncomputable def chunk0041AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0041_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 32)
      (SourceJson.white (chunk0041LeadChars00 ++ (fragment0114654Chars ++ rest))) acc =
      (SourceJson.value (fuel + 31) (fragment0114654Chars ++ rest)).bind
        (chunk0041AfterValue00 (fuel + 31) acc) := by rfl

theorem array_chunk0041 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 32) (SourceJson.white (chunk0041Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 31) (SourceJson.white tail) (chunk0041Push00 acc) := by
  have hinput : chunk0041Chars00 ++ tail = chunk0041LeadChars00 ++ (fragment0114654Chars ++ (chunk0041SuffixChars00 ++ tail)) := by
    simp only [chunk0041Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 32) (SourceJson.white (chunk0041Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 32)
          (SourceJson.white (chunk0041LeadChars00 ++ (fragment0114654Chars ++ (chunk0041SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 32) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 31) (fragment0114654Chars ++ (chunk0041SuffixChars00 ++ tail))).bind
        (chunk0041AfterValue00 (fuel + 31) acc) := array_chunk0041_head fuel (chunk0041SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0114654Value, chunk0041SuffixChars00 ++ tail)).bind
        (chunk0041AfterValue00 (fuel + 31) acc) :=
      congrArg (fun result => result.bind (chunk0041AfterValue00 (fuel + 31) acc))
        (value_fragment0114654 (fuel + 5) (chunk0041SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 31) (SourceJson.white tail) (chunk0041Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0041_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0042_before_reader"
  err.flush

noncomputable def chunk0042LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0042SuffixChars00 : List Char := [',']
noncomputable def chunk0042Chars00 : List Char := chunk0042LeadChars00 ++ fragment0116194Chars ++ chunk0042SuffixChars00
noncomputable def chunk0042Push00 (acc : List SourceJson) : List SourceJson := fragment0116194Value :: acc

noncomputable def chunk0042AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0042_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 31)
      (SourceJson.white (chunk0042LeadChars00 ++ (fragment0116194Chars ++ rest))) acc =
      (SourceJson.value (fuel + 30) (fragment0116194Chars ++ rest)).bind
        (chunk0042AfterValue00 (fuel + 30) acc) := by rfl

theorem array_chunk0042 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 31) (SourceJson.white (chunk0042Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 30) (SourceJson.white tail) (chunk0042Push00 acc) := by
  have hinput : chunk0042Chars00 ++ tail = chunk0042LeadChars00 ++ (fragment0116194Chars ++ (chunk0042SuffixChars00 ++ tail)) := by
    simp only [chunk0042Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 31) (SourceJson.white (chunk0042Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 31)
          (SourceJson.white (chunk0042LeadChars00 ++ (fragment0116194Chars ++ (chunk0042SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 31) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 30) (fragment0116194Chars ++ (chunk0042SuffixChars00 ++ tail))).bind
        (chunk0042AfterValue00 (fuel + 30) acc) := array_chunk0042_head fuel (chunk0042SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0116194Value, chunk0042SuffixChars00 ++ tail)).bind
        (chunk0042AfterValue00 (fuel + 30) acc) :=
      congrArg (fun result => result.bind (chunk0042AfterValue00 (fuel + 30) acc))
        (value_fragment0116194 (fuel + 7) (chunk0042SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 30) (SourceJson.white tail) (chunk0042Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0042_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0043_before_reader"
  err.flush

noncomputable def chunk0043LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0043SuffixChars00 : List Char := [',']
noncomputable def chunk0043Chars00 : List Char := chunk0043LeadChars00 ++ fragment0117358Chars ++ chunk0043SuffixChars00
noncomputable def chunk0043Push00 (acc : List SourceJson) : List SourceJson := fragment0117358Value :: acc

noncomputable def chunk0043AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0043_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 30)
      (SourceJson.white (chunk0043LeadChars00 ++ (fragment0117358Chars ++ rest))) acc =
      (SourceJson.value (fuel + 29) (fragment0117358Chars ++ rest)).bind
        (chunk0043AfterValue00 (fuel + 29) acc) := by rfl

theorem array_chunk0043 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 30) (SourceJson.white (chunk0043Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 29) (SourceJson.white tail) (chunk0043Push00 acc) := by
  have hinput : chunk0043Chars00 ++ tail = chunk0043LeadChars00 ++ (fragment0117358Chars ++ (chunk0043SuffixChars00 ++ tail)) := by
    simp only [chunk0043Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 30) (SourceJson.white (chunk0043Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 30)
          (SourceJson.white (chunk0043LeadChars00 ++ (fragment0117358Chars ++ (chunk0043SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 30) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 29) (fragment0117358Chars ++ (chunk0043SuffixChars00 ++ tail))).bind
        (chunk0043AfterValue00 (fuel + 29) acc) := array_chunk0043_head fuel (chunk0043SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0117358Value, chunk0043SuffixChars00 ++ tail)).bind
        (chunk0043AfterValue00 (fuel + 29) acc) :=
      congrArg (fun result => result.bind (chunk0043AfterValue00 (fuel + 29) acc))
        (value_fragment0117358 (fuel + 9) (chunk0043SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 29) (SourceJson.white tail) (chunk0043Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0043_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0044_before_reader"
  err.flush

noncomputable def chunk0044Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '3', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0044Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['9']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '4']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['3'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['2', '5'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['7']), .number (String.ofList ['9']), .number (String.ofList ['1', '1']), .number (String.ofList ['2', '5'])], .arr [.number (String.ofList ['7']), .number (String.ofList ['9']), .number (String.ofList ['1', '4']), .number (String.ofList ['2', '4'])], .arr [.number (String.ofList ['7']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '4'])], .arr [.number (String.ofList ['9']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5'])], .arr [.number (String.ofList ['1', '1']), .number (String.ofList ['1', '4']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['3']))]) :: (acc)

theorem array_chunk0044 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 29) (SourceJson.white (chunk0044Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 28) (SourceJson.white tail) (chunk0044Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0044_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0045_before_reader"
  err.flush

noncomputable def chunk0045Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '2', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0045Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['1', '1'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['1'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['1', '1'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['7'])], .arr [.number (String.ofList ['1', '1'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['1']))]) :: ((.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['9']), .number (String.ofList ['1', '4']), .number (String.ofList ['2', '4'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['2'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['2', '4'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['7']), .number (String.ofList ['9'])], .arr [.number (String.ofList ['7']), .number (String.ofList ['1', '4'])], .arr [.number (String.ofList ['9']), .number (String.ofList ['2', '4'])], .arr [.number (String.ofList ['1', '4']), .number (String.ofList ['2', '4'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['2']))]) :: (acc))

theorem array_chunk0045 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 28) (SourceJson.white (chunk0045Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 26) (SourceJson.white tail) (chunk0045Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0045_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0046_before_reader"
  err.flush

noncomputable def chunk0046Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0046Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['2'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['1', '2'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['7']), .number (String.ofList ['1', '1'])], .arr [.number (String.ofList ['7']), .number (String.ofList ['1', '2'])], .arr [.number (String.ofList ['1', '1']), .number (String.ofList ['1', '2'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['1']))]) :: (acc)

theorem array_chunk0046 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 26) (SourceJson.white (chunk0046Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 25) (SourceJson.white tail) (chunk0046Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0046_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0047_before_reader"
  err.flush

noncomputable def chunk0047Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0047Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '4'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['3'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['1', '4'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['7']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2'])], .arr [.number (String.ofList ['7']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '4'])], .arr [.number (String.ofList ['7']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '4'])], .arr [.number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '4'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['1']))]) :: (acc)

theorem array_chunk0047 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 25) (SourceJson.white (chunk0047Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 24) (SourceJson.white tail) (chunk0047Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0047_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0040Chars00 ++ chunk0041Chars00 ++ chunk0042Chars00 ++ chunk0043Chars00 ++ chunk0044Chars00 ++ chunk0045Chars00 ++ chunk0046Chars00 ++ chunk0047Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0047Push00 (chunk0046Push00 (chunk0045Push00 (chunk0044Push00 (chunk0043Push00 (chunk0042Push00 (chunk0041Push00 (chunk0040Push00 (acc))))))))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 33) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 24) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0040Chars00 ++ (chunk0041Chars00 ++ (chunk0042Chars00 ++ (chunk0043Chars00 ++ (chunk0044Chars00 ++ (chunk0045Chars00 ++ (chunk0046Chars00 ++ (chunk0047Chars00 ++ (tail)))))))) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 33) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 33) (SourceJson.white (chunk0040Chars00 ++ (chunk0041Chars00 ++ (chunk0042Chars00 ++ (chunk0043Chars00 ++ (chunk0044Chars00 ++ (chunk0045Chars00 ++ (chunk0046Chars00 ++ (chunk0047Chars00 ++ (tail)))))))))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 33) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 32) (SourceJson.white (chunk0041Chars00 ++ (chunk0042Chars00 ++ (chunk0043Chars00 ++ (chunk0044Chars00 ++ (chunk0045Chars00 ++ (chunk0046Chars00 ++ (chunk0047Chars00 ++ (tail))))))))) (chunk0040Push00 (acc)) := array_chunk0040 fuel (chunk0041Chars00 ++ (chunk0042Chars00 ++ (chunk0043Chars00 ++ (chunk0044Chars00 ++ (chunk0045Chars00 ++ (chunk0046Chars00 ++ (chunk0047Chars00 ++ (tail)))))))) (acc)
    _ = SourceJson.array (fuel + 31) (SourceJson.white (chunk0042Chars00 ++ (chunk0043Chars00 ++ (chunk0044Chars00 ++ (chunk0045Chars00 ++ (chunk0046Chars00 ++ (chunk0047Chars00 ++ (tail)))))))) (chunk0041Push00 (chunk0040Push00 (acc))) := array_chunk0041 fuel (chunk0042Chars00 ++ (chunk0043Chars00 ++ (chunk0044Chars00 ++ (chunk0045Chars00 ++ (chunk0046Chars00 ++ (chunk0047Chars00 ++ (tail))))))) (chunk0040Push00 (acc))
    _ = SourceJson.array (fuel + 30) (SourceJson.white (chunk0043Chars00 ++ (chunk0044Chars00 ++ (chunk0045Chars00 ++ (chunk0046Chars00 ++ (chunk0047Chars00 ++ (tail))))))) (chunk0042Push00 (chunk0041Push00 (chunk0040Push00 (acc)))) := array_chunk0042 fuel (chunk0043Chars00 ++ (chunk0044Chars00 ++ (chunk0045Chars00 ++ (chunk0046Chars00 ++ (chunk0047Chars00 ++ (tail)))))) (chunk0041Push00 (chunk0040Push00 (acc)))
    _ = SourceJson.array (fuel + 29) (SourceJson.white (chunk0044Chars00 ++ (chunk0045Chars00 ++ (chunk0046Chars00 ++ (chunk0047Chars00 ++ (tail)))))) (chunk0043Push00 (chunk0042Push00 (chunk0041Push00 (chunk0040Push00 (acc))))) := array_chunk0043 fuel (chunk0044Chars00 ++ (chunk0045Chars00 ++ (chunk0046Chars00 ++ (chunk0047Chars00 ++ (tail))))) (chunk0042Push00 (chunk0041Push00 (chunk0040Push00 (acc))))
    _ = SourceJson.array (fuel + 28) (SourceJson.white (chunk0045Chars00 ++ (chunk0046Chars00 ++ (chunk0047Chars00 ++ (tail))))) (chunk0044Push00 (chunk0043Push00 (chunk0042Push00 (chunk0041Push00 (chunk0040Push00 (acc)))))) := array_chunk0044 fuel (chunk0045Chars00 ++ (chunk0046Chars00 ++ (chunk0047Chars00 ++ (tail)))) (chunk0043Push00 (chunk0042Push00 (chunk0041Push00 (chunk0040Push00 (acc)))))
    _ = SourceJson.array (fuel + 26) (SourceJson.white (chunk0046Chars00 ++ (chunk0047Chars00 ++ (tail)))) (chunk0045Push00 (chunk0044Push00 (chunk0043Push00 (chunk0042Push00 (chunk0041Push00 (chunk0040Push00 (acc))))))) := array_chunk0045 fuel (chunk0046Chars00 ++ (chunk0047Chars00 ++ (tail))) (chunk0044Push00 (chunk0043Push00 (chunk0042Push00 (chunk0041Push00 (chunk0040Push00 (acc))))))
    _ = SourceJson.array (fuel + 25) (SourceJson.white (chunk0047Chars00 ++ (tail))) (chunk0046Push00 (chunk0045Push00 (chunk0044Push00 (chunk0043Push00 (chunk0042Push00 (chunk0041Push00 (chunk0040Push00 (acc)))))))) := array_chunk0046 fuel (chunk0047Chars00 ++ (tail)) (chunk0045Push00 (chunk0044Push00 (chunk0043Push00 (chunk0042Push00 (chunk0041Push00 (chunk0040Push00 (acc)))))))
    _ = SourceJson.array (fuel + 24) (SourceJson.white tail) (blockPush acc) := array_chunk0047 fuel (tail) (chunk0046Push00 (chunk0045Push00 (chunk0044Push00 (chunk0043Push00 (chunk0042Push00 (chunk0041Push00 (chunk0040Push00 (acc))))))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 112672).take 7548 = blockChars := by rfl

theorem block_original_split : sourceRest 112672 = blockChars ++ sourceRest 120220 := by
  calc
    sourceRest 112672 = (sourceRest 112672).take 7548 ++ (sourceRest 112672).drop 7548 :=
      (List.take_append_drop 7548 (sourceRest 112672)).symm
    _ = blockChars ++ (sourceRest 112672).drop 7548 :=
      congrArg (fun part => part ++ (sourceRest 112672).drop 7548) block_original_prefix
    _ = blockChars ++ sourceRest 120220 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 112672 7548)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 33) (SourceJson.white (sourceRest 112672)) acc =
      SourceJson.array (fuel + 24) (SourceJson.white (sourceRest 120220)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 33) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 120220) acc)

#print axioms array_fragment0112954_chunk_000
#print axioms array_fragment0112954_chunk_001
#print axioms array_fragment0112954_chunk_002
#print axioms array_fragment0112954_chunk_003
#print axioms array_fragment0112954_chunk_004
#print axioms value_fragment0112954
#print axioms object_fragment0112678_field_000
#print axioms object_fragment0112678_field_001
#print axioms object_fragment0112678_field_002
#print axioms object_fragment0112678_field_003_header
#print axioms object_fragment0112678_field_003
#print axioms object_fragment0112678_field_004
#print axioms value_fragment0112678
#print axioms array_fragment0114904_chunk_000
#print axioms array_fragment0114904_chunk_001
#print axioms array_fragment0114904_chunk_002
#print axioms array_fragment0114904_chunk_003
#print axioms value_fragment0114904
#print axioms object_fragment0114654_field_000
#print axioms object_fragment0114654_field_001
#print axioms object_fragment0114654_field_002
#print axioms object_fragment0114654_field_003_header
#print axioms object_fragment0114654_field_003
#print axioms object_fragment0114654_field_004
#print axioms value_fragment0114654
#print axioms array_fragment0116418_chunk_000
#print axioms array_fragment0116418_chunk_001
#print axioms array_fragment0116418_chunk_002
#print axioms array_fragment0116418_chunk_003
#print axioms value_fragment0116418
#print axioms object_fragment0116194_field_000
#print axioms object_fragment0116194_field_001
#print axioms object_fragment0116194_field_002
#print axioms object_fragment0116194_field_003_header
#print axioms object_fragment0116194_field_003
#print axioms object_fragment0116194_field_004
#print axioms value_fragment0116194
#print axioms object_fragment0117358_field_000
#print axioms object_fragment0117358_field_001
#print axioms object_fragment0117358_field_002
#print axioms object_fragment0117358_field_003
#print axioms object_fragment0117358_field_004
#print axioms value_fragment0117358
#print axioms array_chunk0040_head
#print axioms array_chunk0040
#print axioms array_chunk0041_head
#print axioms array_chunk0041
#print axioms array_chunk0042_head
#print axioms array_chunk0042
#print axioms array_chunk0043_head
#print axioms array_chunk0043
#print axioms array_chunk0044
#print axioms array_chunk0045
#print axioms array_chunk0046
#print axioms array_chunk0047
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end FaceLedgerBlock005

end ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing
