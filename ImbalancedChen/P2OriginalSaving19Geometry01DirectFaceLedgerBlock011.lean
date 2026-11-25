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

namespace FaceLedgerBlock011

noncomputable def fragment0195563Acc00000 : List SourceJson := []

noncomputable def fragment0195563Chunk000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0195563Chunk000Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '3']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '9']), .number (String.ofList ['3', '6']), .number (String.ofList ['3', '8'])]) :: ((.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '6']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '9']), .number (String.ofList ['3', '2']), .number (String.ofList ['3', '4'])]) :: (acc))

theorem array_fragment0195563_chunk_000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 27) (SourceJson.white (fragment0195563Chunk000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 25) (SourceJson.white tail) (fragment0195563Chunk000Push00 acc) := by
  rfl

noncomputable def fragment0195563Acc00100 : List SourceJson := fragment0195563Chunk000Push00 fragment0195563Acc00000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0195563_array_chunk_000"
  err.flush

noncomputable def fragment0195563Chunk001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0195563Chunk001Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['8']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '6']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '9']), .number (String.ofList ['3', '0']), .number (String.ofList ['3', '2']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '6']), .number (String.ofList ['3', '8'])]) :: ((.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '6']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '8']), .number (String.ofList ['3', '0']), .number (String.ofList ['3', '2']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '6']), .number (String.ofList ['3', '8'])]) :: (acc))

theorem array_fragment0195563_chunk_001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 25) (SourceJson.white (fragment0195563Chunk001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 23) (SourceJson.white tail) (fragment0195563Chunk001Push00 acc) := by
  rfl

noncomputable def fragment0195563Acc00200 : List SourceJson := fragment0195563Chunk001Push00 fragment0195563Acc00100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0195563_array_chunk_001"
  err.flush

noncomputable def fragment0195563Chunk002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0195563Chunk002Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '6']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['3', '0']), .number (String.ofList ['3', '6'])]) :: ((.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '6']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '9']), .number (String.ofList ['3', '0']), .number (String.ofList ['3', '2']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '6']), .number (String.ofList ['3', '8'])]) :: (acc))

theorem array_fragment0195563_chunk_002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 23) (SourceJson.white (fragment0195563Chunk002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 21) (SourceJson.white tail) (fragment0195563Chunk002Push00 acc) := by
  rfl

noncomputable def fragment0195563Acc00300 : List SourceJson := fragment0195563Chunk002Push00 fragment0195563Acc00200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0195563_array_chunk_002"
  err.flush

noncomputable def fragment0195563Chunk003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0195563Chunk003Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '9']), .number (String.ofList ['3', '0']), .number (String.ofList ['3', '2']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '6']), .number (String.ofList ['3', '8'])]) :: ((.arr [.number (String.ofList ['1']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '6']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '9']), .number (String.ofList ['3', '0']), .number (String.ofList ['3', '2']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '6']), .number (String.ofList ['3', '8'])]) :: (acc))

theorem array_fragment0195563_chunk_003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 21) (SourceJson.white (fragment0195563Chunk003Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 19) (SourceJson.white tail) (fragment0195563Chunk003Push00 acc) := by
  rfl

noncomputable def fragment0195563Acc00400 : List SourceJson := fragment0195563Chunk003Push00 fragment0195563Acc00300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0195563_array_chunk_003"
  err.flush

noncomputable def fragment0195563Chunk004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']']
noncomputable def fragment0195563Chunk004Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1', '6']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['3', '0']), .number (String.ofList ['3', '2'])]) :: ((.arr [.number (String.ofList ['5']), .number (String.ofList ['1', '3']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '9']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '8'])]) :: (acc))

theorem array_fragment0195563_chunk_004 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 19) (SourceJson.white (fragment0195563Chunk004Chars00 ++ tail)) acc =
      .ok (.arr ((fragment0195563Chunk004Push00 acc).reverse), tail) := by
  rfl

noncomputable def fragment0195563Acc00500 : List SourceJson := fragment0195563Chunk004Push00 fragment0195563Acc00400

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0195563_array_chunk_004"
  err.flush

noncomputable def fragment0195563Chars : List Char := '[' :: (fragment0195563Chunk000Chars00 ++ fragment0195563Chunk001Chars00 ++ fragment0195563Chunk002Chars00 ++ fragment0195563Chunk003Chars00 ++ fragment0195563Chunk004Chars00)
noncomputable def fragment0195563Value : SourceJson := .arr (fragment0195563Acc00500.reverse)

theorem value_fragment0195563 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 28) (fragment0195563Chars ++ tail) =
      .ok (fragment0195563Value, tail) := by
  have hinput : fragment0195563Chars ++ tail = '[' :: (fragment0195563Chunk000Chars00 ++ (fragment0195563Chunk001Chars00 ++ (fragment0195563Chunk002Chars00 ++ (fragment0195563Chunk003Chars00 ++ (fragment0195563Chunk004Chars00 ++ (tail)))))) := by
    simp only [fragment0195563Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 28) (fragment0195563Chars ++ tail) =
        SourceJson.value (fuel + 28) ('[' :: (fragment0195563Chunk000Chars00 ++ (fragment0195563Chunk001Chars00 ++ (fragment0195563Chunk002Chars00 ++ (fragment0195563Chunk003Chars00 ++ (fragment0195563Chunk004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 28)) hinput
    _ = SourceJson.array (fuel + 27) (SourceJson.white (fragment0195563Chunk000Chars00 ++ (fragment0195563Chunk001Chars00 ++ (fragment0195563Chunk002Chars00 ++ (fragment0195563Chunk003Chars00 ++ (fragment0195563Chunk004Chars00 ++ (tail))))))) fragment0195563Acc00000 := by rfl
    _ = SourceJson.array (fuel + 25) (SourceJson.white (fragment0195563Chunk001Chars00 ++ (fragment0195563Chunk002Chars00 ++ (fragment0195563Chunk003Chars00 ++ (fragment0195563Chunk004Chars00 ++ (tail)))))) fragment0195563Acc00100 := array_fragment0195563_chunk_000 fuel (fragment0195563Chunk001Chars00 ++ (fragment0195563Chunk002Chars00 ++ (fragment0195563Chunk003Chars00 ++ (fragment0195563Chunk004Chars00 ++ (tail))))) fragment0195563Acc00000
    _ = SourceJson.array (fuel + 23) (SourceJson.white (fragment0195563Chunk002Chars00 ++ (fragment0195563Chunk003Chars00 ++ (fragment0195563Chunk004Chars00 ++ (tail))))) fragment0195563Acc00200 := array_fragment0195563_chunk_001 fuel (fragment0195563Chunk002Chars00 ++ (fragment0195563Chunk003Chars00 ++ (fragment0195563Chunk004Chars00 ++ (tail)))) fragment0195563Acc00100
    _ = SourceJson.array (fuel + 21) (SourceJson.white (fragment0195563Chunk003Chars00 ++ (fragment0195563Chunk004Chars00 ++ (tail)))) fragment0195563Acc00300 := array_fragment0195563_chunk_002 fuel (fragment0195563Chunk003Chars00 ++ (fragment0195563Chunk004Chars00 ++ (tail))) fragment0195563Acc00200
    _ = SourceJson.array (fuel + 19) (SourceJson.white (fragment0195563Chunk004Chars00 ++ (tail))) fragment0195563Acc00400 := array_fragment0195563_chunk_003 fuel (fragment0195563Chunk004Chars00 ++ (tail)) fragment0195563Acc00300
    _ = .ok (fragment0195563Value, tail) := array_fragment0195563_chunk_004 fuel (tail) fragment0195563Acc00400

noncomputable def fragment0195211Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0195211Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0195211Field000Value00 : SourceJson := .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '6']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '9']), .number (String.ofList ['3', '0']), .number (String.ofList ['3', '2']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '6']), .number (String.ofList ['3', '8'])]
noncomputable def fragment0195211Acc00100 : List (String × SourceJson) := (fragment0195211Field000Key00, fragment0195211Field000Value00) :: fragment0195211Acc00000
noncomputable def fragment0195211Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0195211_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 32) (SourceJson.white (fragment0195211Field000Chars00 ++ tail)) fragment0195211Acc00000 =
      SourceJson.object (fuel + 31) (SourceJson.white tail) fragment0195211Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0195211_object_field_000"
  err.flush

noncomputable def fragment0195211Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0195211Field001Value00 : SourceJson := .number (String.ofList ['7'])
noncomputable def fragment0195211Acc00200 : List (String × SourceJson) := (fragment0195211Field001Key00, fragment0195211Field001Value00) :: fragment0195211Acc00100
noncomputable def fragment0195211Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '7', ',']

theorem object_fragment0195211_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 31) (SourceJson.white (fragment0195211Field001Chars00 ++ tail)) fragment0195211Acc00100 =
      SourceJson.object (fuel + 30) (SourceJson.white tail) fragment0195211Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0195211_object_field_001"
  err.flush

noncomputable def fragment0195211Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0195211Field002Value00 : SourceJson := .number (String.ofList ['3', '8'])
noncomputable def fragment0195211Acc00300 : List (String × SourceJson) := (fragment0195211Field002Key00, fragment0195211Field002Value00) :: fragment0195211Acc00200
noncomputable def fragment0195211Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '3', '8', ',']

theorem object_fragment0195211_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 30) (SourceJson.white (fragment0195211Field002Chars00 ++ tail)) fragment0195211Acc00200 =
      SourceJson.object (fuel + 29) (SourceJson.white tail) fragment0195211Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0195211_object_field_002"
  err.flush

noncomputable def fragment0195211Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0195211Field003Value00 : SourceJson := fragment0195563Value
noncomputable def fragment0195211Acc00400 : List (String × SourceJson) := (fragment0195211Field003Key00, fragment0195211Field003Value00) :: fragment0195211Acc00300
noncomputable def fragment0195211Field003HeaderChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ']
noncomputable def fragment0195211Field003SuffixChars00 : List Char := [',']
noncomputable def fragment0195211Field003Chars00 : List Char := fragment0195211Field003HeaderChars00 ++ fragment0195563Chars ++ fragment0195211Field003SuffixChars00

noncomputable def fragment0195211Field003AfterValue00 (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending => .ok (.obj (((fragment0195211Field003Key00, result.1) :: fragment0195211Acc00300).reverse), ending)
  | ',' :: ending => SourceJson.object fuel (SourceJson.white ending) ((fragment0195211Field003Key00, result.1) :: fragment0195211Acc00300)
  | _ => .error "object separator missing"

theorem object_fragment0195211_field_003_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 29) (SourceJson.white (fragment0195211Field003HeaderChars00 ++ rest)) fragment0195211Acc00300 =
      (SourceJson.value (fuel + 28) rest).bind (fragment0195211Field003AfterValue00 (fuel + 28)) := by rfl

theorem object_fragment0195211_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 29) (SourceJson.white (fragment0195211Field003Chars00 ++ tail)) fragment0195211Acc00300 =
      SourceJson.object (fuel + 28) (SourceJson.white tail) fragment0195211Acc00400 := by
  have hinput : fragment0195211Field003Chars00 ++ tail = fragment0195211Field003HeaderChars00 ++ (fragment0195563Chars ++ (fragment0195211Field003SuffixChars00 ++ tail)) := by
    simp only [fragment0195211Field003Chars00, List.append_assoc]
  calc
    SourceJson.object (fuel + 29) (SourceJson.white (fragment0195211Field003Chars00 ++ tail)) fragment0195211Acc00300 =
        SourceJson.object (fuel + 29)
          (SourceJson.white (fragment0195211Field003HeaderChars00 ++ (fragment0195563Chars ++ (fragment0195211Field003SuffixChars00 ++ tail)))) fragment0195211Acc00300 :=
      congrArg (fun s => SourceJson.object (fuel + 29) (SourceJson.white s) fragment0195211Acc00300) hinput
    _ = (SourceJson.value (fuel + 28) (fragment0195563Chars ++ (fragment0195211Field003SuffixChars00 ++ tail))).bind
        (fragment0195211Field003AfterValue00 (fuel + 28)) := object_fragment0195211_field_003_header fuel (fragment0195563Chars ++ (fragment0195211Field003SuffixChars00 ++ tail))
    _ = (Except.ok (fragment0195563Value, fragment0195211Field003SuffixChars00 ++ tail)).bind (fragment0195211Field003AfterValue00 (fuel + 28)) :=
      congrArg (fun result => result.bind (fragment0195211Field003AfterValue00 (fuel + 28)))
        (value_fragment0195563 (fuel + 0) (fragment0195211Field003SuffixChars00 ++ tail))
    _ = SourceJson.object (fuel + 28) (SourceJson.white tail) fragment0195211Acc00400 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0195211_object_field_003"
  err.flush

noncomputable def fragment0195211Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0195211Field004Value00 : SourceJson := .number (String.ofList ['1', '8'])
noncomputable def fragment0195211Acc00500 : List (String × SourceJson) := (fragment0195211Field004Key00, fragment0195211Field004Value00) :: fragment0195211Acc00400
noncomputable def fragment0195211Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '8', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0195211_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 28) (SourceJson.white (fragment0195211Field004Chars00 ++ tail)) fragment0195211Acc00400 =
      .ok (.obj (fragment0195211Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0195211_object_field_004"
  err.flush

noncomputable def fragment0195211Chars : List Char := '{' :: (fragment0195211Field000Chars00 ++ fragment0195211Field001Chars00 ++ fragment0195211Field002Chars00 ++ fragment0195211Field003Chars00 ++ fragment0195211Field004Chars00)
noncomputable def fragment0195211Value : SourceJson := .obj (fragment0195211Acc00500.reverse)

theorem value_fragment0195211 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 33) (fragment0195211Chars ++ tail) =
      .ok (fragment0195211Value, tail) := by
  have hinput : fragment0195211Chars ++ tail = '{' :: (fragment0195211Field000Chars00 ++ (fragment0195211Field001Chars00 ++ (fragment0195211Field002Chars00 ++ (fragment0195211Field003Chars00 ++ (fragment0195211Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0195211Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 33) (fragment0195211Chars ++ tail) =
        SourceJson.value (fuel + 33) ('{' :: (fragment0195211Field000Chars00 ++ (fragment0195211Field001Chars00 ++ (fragment0195211Field002Chars00 ++ (fragment0195211Field003Chars00 ++ (fragment0195211Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 33)) hinput
    _ = SourceJson.object (fuel + 32) (SourceJson.white (fragment0195211Field000Chars00 ++ (fragment0195211Field001Chars00 ++ (fragment0195211Field002Chars00 ++ (fragment0195211Field003Chars00 ++ (fragment0195211Field004Chars00 ++ (tail))))))) fragment0195211Acc00000 := by rfl
    _ = SourceJson.object (fuel + 31) (SourceJson.white (fragment0195211Field001Chars00 ++ (fragment0195211Field002Chars00 ++ (fragment0195211Field003Chars00 ++ (fragment0195211Field004Chars00 ++ (tail)))))) fragment0195211Acc00100 := object_fragment0195211_field_000 fuel (fragment0195211Field001Chars00 ++ (fragment0195211Field002Chars00 ++ (fragment0195211Field003Chars00 ++ (fragment0195211Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 30) (SourceJson.white (fragment0195211Field002Chars00 ++ (fragment0195211Field003Chars00 ++ (fragment0195211Field004Chars00 ++ (tail))))) fragment0195211Acc00200 := object_fragment0195211_field_001 fuel (fragment0195211Field002Chars00 ++ (fragment0195211Field003Chars00 ++ (fragment0195211Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 29) (SourceJson.white (fragment0195211Field003Chars00 ++ (fragment0195211Field004Chars00 ++ (tail)))) fragment0195211Acc00300 := object_fragment0195211_field_002 fuel (fragment0195211Field003Chars00 ++ (fragment0195211Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 28) (SourceJson.white (fragment0195211Field004Chars00 ++ (tail))) fragment0195211Acc00400 := object_fragment0195211_field_003 fuel (fragment0195211Field004Chars00 ++ (tail))
    _ = .ok (fragment0195211Value, tail) := object_fragment0195211_field_004 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0031_before_reader"
  err.flush

noncomputable def chunk0031LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0031SuffixChars00 : List Char := [',']
noncomputable def chunk0031Chars00 : List Char := chunk0031LeadChars00 ++ fragment0195211Chars ++ chunk0031SuffixChars00
noncomputable def chunk0031Push00 (acc : List SourceJson) : List SourceJson := fragment0195211Value :: acc

noncomputable def chunk0031AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0031_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 62)
      (SourceJson.white (chunk0031LeadChars00 ++ (fragment0195211Chars ++ rest))) acc =
      (SourceJson.value (fuel + 61) (fragment0195211Chars ++ rest)).bind
        (chunk0031AfterValue00 (fuel + 61) acc) := by rfl

theorem array_chunk0031 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 62) (SourceJson.white (chunk0031Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 61) (SourceJson.white tail) (chunk0031Push00 acc) := by
  have hinput : chunk0031Chars00 ++ tail = chunk0031LeadChars00 ++ (fragment0195211Chars ++ (chunk0031SuffixChars00 ++ tail)) := by
    simp only [chunk0031Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 62) (SourceJson.white (chunk0031Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 62)
          (SourceJson.white (chunk0031LeadChars00 ++ (fragment0195211Chars ++ (chunk0031SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 62) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 61) (fragment0195211Chars ++ (chunk0031SuffixChars00 ++ tail))).bind
        (chunk0031AfterValue00 (fuel + 61) acc) := array_chunk0031_head fuel (chunk0031SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0195211Value, chunk0031SuffixChars00 ++ tail)).bind
        (chunk0031AfterValue00 (fuel + 61) acc) :=
      congrArg (fun result => result.bind (chunk0031AfterValue00 (fuel + 61) acc))
        (value_fragment0195211 (fuel + 28) (chunk0031SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 61) (SourceJson.white tail) (chunk0031Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0031_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0031Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0031Push00 (acc)

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 62) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 61) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0031Chars00 ++ (tail) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 62) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 62) (SourceJson.white (chunk0031Chars00 ++ (tail))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 62) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 61) (SourceJson.white tail) (blockPush acc) := array_chunk0031 fuel (tail) (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 195205).take 2691 = blockChars := by rfl

theorem block_original_split : sourceRest 195205 = blockChars ++ sourceRest 197896 := by
  calc
    sourceRest 195205 = (sourceRest 195205).take 2691 ++ (sourceRest 195205).drop 2691 :=
      (List.take_append_drop 2691 (sourceRest 195205)).symm
    _ = blockChars ++ (sourceRest 195205).drop 2691 :=
      congrArg (fun part => part ++ (sourceRest 195205).drop 2691) block_original_prefix
    _ = blockChars ++ sourceRest 197896 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 195205 2691)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 62) (SourceJson.white (sourceRest 195205)) acc =
      SourceJson.array (fuel + 61) (SourceJson.white (sourceRest 197896)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 62) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 197896) acc)

#print axioms array_fragment0195563_chunk_000
#print axioms array_fragment0195563_chunk_001
#print axioms array_fragment0195563_chunk_002
#print axioms array_fragment0195563_chunk_003
#print axioms array_fragment0195563_chunk_004
#print axioms value_fragment0195563
#print axioms object_fragment0195211_field_000
#print axioms object_fragment0195211_field_001
#print axioms object_fragment0195211_field_002
#print axioms object_fragment0195211_field_003_header
#print axioms object_fragment0195211_field_003
#print axioms object_fragment0195211_field_004
#print axioms value_fragment0195211
#print axioms array_chunk0031_head
#print axioms array_chunk0031
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end FaceLedgerBlock011

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
