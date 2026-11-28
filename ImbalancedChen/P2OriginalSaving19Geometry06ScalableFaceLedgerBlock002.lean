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

namespace FaceLedgerBlock002

noncomputable def fragment0094818Acc00000 : List SourceJson := []

noncomputable def fragment0094818Chunk000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0094818Chunk000Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['6']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '7']), .number (String.ofList ['2', '9'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['6']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '5']), .number (String.ofList ['2', '0'])]) :: (acc))

theorem array_fragment0094818_chunk_000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 21) (SourceJson.white (fragment0094818Chunk000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 19) (SourceJson.white tail) (fragment0094818Chunk000Push00 acc) := by
  rfl

noncomputable def fragment0094818Acc00100 : List SourceJson := fragment0094818Chunk000Push00 fragment0094818Acc00000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0094818_array_chunk_000"
  err.flush

noncomputable def fragment0094818Chunk001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0094818Chunk001Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['6']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '5']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '7']), .number (String.ofList ['2', '9'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '5']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '7'])]) :: (acc))

theorem array_fragment0094818_chunk_001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 19) (SourceJson.white (fragment0094818Chunk001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 17) (SourceJson.white tail) (fragment0094818Chunk001Push00 acc) := by
  rfl

noncomputable def fragment0094818Acc00200 : List SourceJson := fragment0094818Chunk001Push00 fragment0094818Acc00100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0094818_array_chunk_001"
  err.flush

noncomputable def fragment0094818Chunk002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0094818Chunk002Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['6']), .number (String.ofList ['8']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '5']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '7']), .number (String.ofList ['2', '9'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['4']), .number (String.ofList ['6']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '3']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '9'])]) :: (acc))

theorem array_fragment0094818_chunk_002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 17) (SourceJson.white (fragment0094818Chunk002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 15) (SourceJson.white tail) (fragment0094818Chunk002Push00 acc) := by
  rfl

noncomputable def fragment0094818Acc00300 : List SourceJson := fragment0094818Chunk002Push00 fragment0094818Acc00200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0094818_array_chunk_002"
  err.flush

noncomputable def fragment0094818Chunk003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']']
noncomputable def fragment0094818Chunk003Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '5']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '7']), .number (String.ofList ['2', '9'])]) :: ((.arr [.number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['6']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '5']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '7']), .number (String.ofList ['2', '9'])]) :: (acc))

theorem array_fragment0094818_chunk_003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 15) (SourceJson.white (fragment0094818Chunk003Chars00 ++ tail)) acc =
      .ok (.arr ((fragment0094818Chunk003Push00 acc).reverse), tail) := by
  rfl

noncomputable def fragment0094818Acc00400 : List SourceJson := fragment0094818Chunk003Push00 fragment0094818Acc00300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0094818_array_chunk_003"
  err.flush

noncomputable def fragment0094818Chars : List Char := '[' :: (fragment0094818Chunk000Chars00 ++ fragment0094818Chunk001Chars00 ++ fragment0094818Chunk002Chars00 ++ fragment0094818Chunk003Chars00)
noncomputable def fragment0094818Value : SourceJson := .arr (fragment0094818Acc00400.reverse)

theorem value_fragment0094818 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 22) (fragment0094818Chars ++ tail) =
      .ok (fragment0094818Value, tail) := by
  have hinput : fragment0094818Chars ++ tail = '[' :: (fragment0094818Chunk000Chars00 ++ (fragment0094818Chunk001Chars00 ++ (fragment0094818Chunk002Chars00 ++ (fragment0094818Chunk003Chars00 ++ (tail))))) := by
    simp only [fragment0094818Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 22) (fragment0094818Chars ++ tail) =
        SourceJson.value (fuel + 22) ('[' :: (fragment0094818Chunk000Chars00 ++ (fragment0094818Chunk001Chars00 ++ (fragment0094818Chunk002Chars00 ++ (fragment0094818Chunk003Chars00 ++ (tail)))))) :=
      congrArg (SourceJson.value (fuel + 22)) hinput
    _ = SourceJson.array (fuel + 21) (SourceJson.white (fragment0094818Chunk000Chars00 ++ (fragment0094818Chunk001Chars00 ++ (fragment0094818Chunk002Chars00 ++ (fragment0094818Chunk003Chars00 ++ (tail)))))) fragment0094818Acc00000 := by rfl
    _ = SourceJson.array (fuel + 19) (SourceJson.white (fragment0094818Chunk001Chars00 ++ (fragment0094818Chunk002Chars00 ++ (fragment0094818Chunk003Chars00 ++ (tail))))) fragment0094818Acc00100 := array_fragment0094818_chunk_000 fuel (fragment0094818Chunk001Chars00 ++ (fragment0094818Chunk002Chars00 ++ (fragment0094818Chunk003Chars00 ++ (tail)))) fragment0094818Acc00000
    _ = SourceJson.array (fuel + 17) (SourceJson.white (fragment0094818Chunk002Chars00 ++ (fragment0094818Chunk003Chars00 ++ (tail)))) fragment0094818Acc00200 := array_fragment0094818_chunk_001 fuel (fragment0094818Chunk002Chars00 ++ (fragment0094818Chunk003Chars00 ++ (tail))) fragment0094818Acc00100
    _ = SourceJson.array (fuel + 15) (SourceJson.white (fragment0094818Chunk003Chars00 ++ (tail))) fragment0094818Acc00300 := array_fragment0094818_chunk_002 fuel (fragment0094818Chunk003Chars00 ++ (tail)) fragment0094818Acc00200
    _ = .ok (fragment0094818Value, tail) := array_fragment0094818_chunk_003 fuel (tail) fragment0094818Acc00300

noncomputable def fragment0094533Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0094533Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0094533Field000Value00 : SourceJson := .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['6']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '5']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '7']), .number (String.ofList ['2', '9'])]
noncomputable def fragment0094533Acc00100 : List (String × SourceJson) := (fragment0094533Field000Key00, fragment0094533Field000Value00) :: fragment0094533Acc00000
noncomputable def fragment0094533Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0094533_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 26) (SourceJson.white (fragment0094533Field000Chars00 ++ tail)) fragment0094533Acc00000 =
      SourceJson.object (fuel + 25) (SourceJson.white tail) fragment0094533Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0094533_object_field_000"
  err.flush

noncomputable def fragment0094533Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0094533Field001Value00 : SourceJson := .number (String.ofList ['6'])
noncomputable def fragment0094533Acc00200 : List (String × SourceJson) := (fragment0094533Field001Key00, fragment0094533Field001Value00) :: fragment0094533Acc00100
noncomputable def fragment0094533Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '6', ',']

theorem object_fragment0094533_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 25) (SourceJson.white (fragment0094533Field001Chars00 ++ tail)) fragment0094533Acc00100 =
      SourceJson.object (fuel + 24) (SourceJson.white tail) fragment0094533Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0094533_object_field_001"
  err.flush

noncomputable def fragment0094533Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0094533Field002Value00 : SourceJson := .number (String.ofList ['2', '9'])
noncomputable def fragment0094533Acc00300 : List (String × SourceJson) := (fragment0094533Field002Key00, fragment0094533Field002Value00) :: fragment0094533Acc00200
noncomputable def fragment0094533Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '2', '9', ',']

theorem object_fragment0094533_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 24) (SourceJson.white (fragment0094533Field002Chars00 ++ tail)) fragment0094533Acc00200 =
      SourceJson.object (fuel + 23) (SourceJson.white tail) fragment0094533Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0094533_object_field_002"
  err.flush

noncomputable def fragment0094533Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0094533Field003Value00 : SourceJson := fragment0094818Value
noncomputable def fragment0094533Acc00400 : List (String × SourceJson) := (fragment0094533Field003Key00, fragment0094533Field003Value00) :: fragment0094533Acc00300
noncomputable def fragment0094533Field003HeaderChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ']
noncomputable def fragment0094533Field003SuffixChars00 : List Char := [',']
noncomputable def fragment0094533Field003Chars00 : List Char := fragment0094533Field003HeaderChars00 ++ fragment0094818Chars ++ fragment0094533Field003SuffixChars00

noncomputable def fragment0094533Field003AfterValue00 (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending => .ok (.obj (((fragment0094533Field003Key00, result.1) :: fragment0094533Acc00300).reverse), ending)
  | ',' :: ending => SourceJson.object fuel (SourceJson.white ending) ((fragment0094533Field003Key00, result.1) :: fragment0094533Acc00300)
  | _ => .error "object separator missing"

theorem object_fragment0094533_field_003_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 23) (SourceJson.white (fragment0094533Field003HeaderChars00 ++ rest)) fragment0094533Acc00300 =
      (SourceJson.value (fuel + 22) rest).bind (fragment0094533Field003AfterValue00 (fuel + 22)) := by rfl

theorem object_fragment0094533_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 23) (SourceJson.white (fragment0094533Field003Chars00 ++ tail)) fragment0094533Acc00300 =
      SourceJson.object (fuel + 22) (SourceJson.white tail) fragment0094533Acc00400 := by
  have hinput : fragment0094533Field003Chars00 ++ tail = fragment0094533Field003HeaderChars00 ++ (fragment0094818Chars ++ (fragment0094533Field003SuffixChars00 ++ tail)) := by
    simp only [fragment0094533Field003Chars00, List.append_assoc]
  calc
    SourceJson.object (fuel + 23) (SourceJson.white (fragment0094533Field003Chars00 ++ tail)) fragment0094533Acc00300 =
        SourceJson.object (fuel + 23)
          (SourceJson.white (fragment0094533Field003HeaderChars00 ++ (fragment0094818Chars ++ (fragment0094533Field003SuffixChars00 ++ tail)))) fragment0094533Acc00300 :=
      congrArg (fun s => SourceJson.object (fuel + 23) (SourceJson.white s) fragment0094533Acc00300) hinput
    _ = (SourceJson.value (fuel + 22) (fragment0094818Chars ++ (fragment0094533Field003SuffixChars00 ++ tail))).bind
        (fragment0094533Field003AfterValue00 (fuel + 22)) := object_fragment0094533_field_003_header fuel (fragment0094818Chars ++ (fragment0094533Field003SuffixChars00 ++ tail))
    _ = (Except.ok (fragment0094818Value, fragment0094533Field003SuffixChars00 ++ tail)).bind (fragment0094533Field003AfterValue00 (fuel + 22)) :=
      congrArg (fun result => result.bind (fragment0094533Field003AfterValue00 (fuel + 22)))
        (value_fragment0094818 (fuel + 0) (fragment0094533Field003SuffixChars00 ++ tail))
    _ = SourceJson.object (fuel + 22) (SourceJson.white tail) fragment0094533Acc00400 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0094533_object_field_003"
  err.flush

noncomputable def fragment0094533Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0094533Field004Value00 : SourceJson := .number (String.ofList ['1', '5'])
noncomputable def fragment0094533Acc00500 : List (String × SourceJson) := (fragment0094533Field004Key00, fragment0094533Field004Value00) :: fragment0094533Acc00400
noncomputable def fragment0094533Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '5', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0094533_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 22) (SourceJson.white (fragment0094533Field004Chars00 ++ tail)) fragment0094533Acc00400 =
      .ok (.obj (fragment0094533Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0094533_object_field_004"
  err.flush

noncomputable def fragment0094533Chars : List Char := '{' :: (fragment0094533Field000Chars00 ++ fragment0094533Field001Chars00 ++ fragment0094533Field002Chars00 ++ fragment0094533Field003Chars00 ++ fragment0094533Field004Chars00)
noncomputable def fragment0094533Value : SourceJson := .obj (fragment0094533Acc00500.reverse)

theorem value_fragment0094533 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 27) (fragment0094533Chars ++ tail) =
      .ok (fragment0094533Value, tail) := by
  have hinput : fragment0094533Chars ++ tail = '{' :: (fragment0094533Field000Chars00 ++ (fragment0094533Field001Chars00 ++ (fragment0094533Field002Chars00 ++ (fragment0094533Field003Chars00 ++ (fragment0094533Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0094533Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 27) (fragment0094533Chars ++ tail) =
        SourceJson.value (fuel + 27) ('{' :: (fragment0094533Field000Chars00 ++ (fragment0094533Field001Chars00 ++ (fragment0094533Field002Chars00 ++ (fragment0094533Field003Chars00 ++ (fragment0094533Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 27)) hinput
    _ = SourceJson.object (fuel + 26) (SourceJson.white (fragment0094533Field000Chars00 ++ (fragment0094533Field001Chars00 ++ (fragment0094533Field002Chars00 ++ (fragment0094533Field003Chars00 ++ (fragment0094533Field004Chars00 ++ (tail))))))) fragment0094533Acc00000 := by rfl
    _ = SourceJson.object (fuel + 25) (SourceJson.white (fragment0094533Field001Chars00 ++ (fragment0094533Field002Chars00 ++ (fragment0094533Field003Chars00 ++ (fragment0094533Field004Chars00 ++ (tail)))))) fragment0094533Acc00100 := object_fragment0094533_field_000 fuel (fragment0094533Field001Chars00 ++ (fragment0094533Field002Chars00 ++ (fragment0094533Field003Chars00 ++ (fragment0094533Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 24) (SourceJson.white (fragment0094533Field002Chars00 ++ (fragment0094533Field003Chars00 ++ (fragment0094533Field004Chars00 ++ (tail))))) fragment0094533Acc00200 := object_fragment0094533_field_001 fuel (fragment0094533Field002Chars00 ++ (fragment0094533Field003Chars00 ++ (fragment0094533Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 23) (SourceJson.white (fragment0094533Field003Chars00 ++ (fragment0094533Field004Chars00 ++ (tail)))) fragment0094533Acc00300 := object_fragment0094533_field_002 fuel (fragment0094533Field003Chars00 ++ (fragment0094533Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 22) (SourceJson.white (fragment0094533Field004Chars00 ++ (tail))) fragment0094533Acc00400 := object_fragment0094533_field_003 fuel (fragment0094533Field004Chars00 ++ (tail))
    _ = .ok (fragment0094533Value, tail) := object_fragment0094533_field_004 fuel (tail)

noncomputable def fragment0096355Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0096355Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0096355Field000Value00 : SourceJson := .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '5'])]
noncomputable def fragment0096355Acc00100 : List (String × SourceJson) := (fragment0096355Field000Key00, fragment0096355Field000Value00) :: fragment0096355Acc00000
noncomputable def fragment0096355Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0096355_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 18) (SourceJson.white (fragment0096355Field000Chars00 ++ tail)) fragment0096355Acc00000 =
      SourceJson.object (fuel + 17) (SourceJson.white tail) fragment0096355Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0096355_object_field_000"
  err.flush

noncomputable def fragment0096355Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0096355Field001Value00 : SourceJson := .number (String.ofList ['4'])
noncomputable def fragment0096355Acc00200 : List (String × SourceJson) := (fragment0096355Field001Key00, fragment0096355Field001Value00) :: fragment0096355Acc00100
noncomputable def fragment0096355Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '4', ',']

theorem object_fragment0096355_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 17) (SourceJson.white (fragment0096355Field001Chars00 ++ tail)) fragment0096355Acc00100 =
      SourceJson.object (fuel + 16) (SourceJson.white tail) fragment0096355Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0096355_object_field_001"
  err.flush

noncomputable def fragment0096355Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0096355Field002Value00 : SourceJson := .number (String.ofList ['1', '5'])
noncomputable def fragment0096355Acc00300 : List (String × SourceJson) := (fragment0096355Field002Key00, fragment0096355Field002Value00) :: fragment0096355Acc00200
noncomputable def fragment0096355Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '1', '5', ',']

theorem object_fragment0096355_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 16) (SourceJson.white (fragment0096355Field002Chars00 ++ tail)) fragment0096355Acc00200 =
      SourceJson.object (fuel + 15) (SourceJson.white tail) fragment0096355Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0096355_object_field_002"
  err.flush

noncomputable def fragment0096355Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0096355Field003Value00 : SourceJson := .arr [.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['4'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '5'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['4']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '3'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['8']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '5'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '5'])], .arr [.number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '5'])]]
noncomputable def fragment0096355Acc00400 : List (String × SourceJson) := (fragment0096355Field003Key00, fragment0096355Field003Value00) :: fragment0096355Acc00300
noncomputable def fragment0096355Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0096355_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 15) (SourceJson.white (fragment0096355Field003Chars00 ++ tail)) fragment0096355Acc00300 =
      SourceJson.object (fuel + 14) (SourceJson.white tail) fragment0096355Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0096355_object_field_003"
  err.flush

noncomputable def fragment0096355Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0096355Field004Value00 : SourceJson := .number (String.ofList ['4'])
noncomputable def fragment0096355Acc00500 : List (String × SourceJson) := (fragment0096355Field004Key00, fragment0096355Field004Value00) :: fragment0096355Acc00400
noncomputable def fragment0096355Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0096355_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 14) (SourceJson.white (fragment0096355Field004Chars00 ++ tail)) fragment0096355Acc00400 =
      .ok (.obj (fragment0096355Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0096355_object_field_004"
  err.flush

noncomputable def fragment0096355Chars : List Char := '{' :: (fragment0096355Field000Chars00 ++ fragment0096355Field001Chars00 ++ fragment0096355Field002Chars00 ++ fragment0096355Field003Chars00 ++ fragment0096355Field004Chars00)
noncomputable def fragment0096355Value : SourceJson := .obj (fragment0096355Acc00500.reverse)

theorem value_fragment0096355 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 19) (fragment0096355Chars ++ tail) =
      .ok (fragment0096355Value, tail) := by
  have hinput : fragment0096355Chars ++ tail = '{' :: (fragment0096355Field000Chars00 ++ (fragment0096355Field001Chars00 ++ (fragment0096355Field002Chars00 ++ (fragment0096355Field003Chars00 ++ (fragment0096355Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0096355Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 19) (fragment0096355Chars ++ tail) =
        SourceJson.value (fuel + 19) ('{' :: (fragment0096355Field000Chars00 ++ (fragment0096355Field001Chars00 ++ (fragment0096355Field002Chars00 ++ (fragment0096355Field003Chars00 ++ (fragment0096355Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 19)) hinput
    _ = SourceJson.object (fuel + 18) (SourceJson.white (fragment0096355Field000Chars00 ++ (fragment0096355Field001Chars00 ++ (fragment0096355Field002Chars00 ++ (fragment0096355Field003Chars00 ++ (fragment0096355Field004Chars00 ++ (tail))))))) fragment0096355Acc00000 := by rfl
    _ = SourceJson.object (fuel + 17) (SourceJson.white (fragment0096355Field001Chars00 ++ (fragment0096355Field002Chars00 ++ (fragment0096355Field003Chars00 ++ (fragment0096355Field004Chars00 ++ (tail)))))) fragment0096355Acc00100 := object_fragment0096355_field_000 fuel (fragment0096355Field001Chars00 ++ (fragment0096355Field002Chars00 ++ (fragment0096355Field003Chars00 ++ (fragment0096355Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 16) (SourceJson.white (fragment0096355Field002Chars00 ++ (fragment0096355Field003Chars00 ++ (fragment0096355Field004Chars00 ++ (tail))))) fragment0096355Acc00200 := object_fragment0096355_field_001 fuel (fragment0096355Field002Chars00 ++ (fragment0096355Field003Chars00 ++ (fragment0096355Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 15) (SourceJson.white (fragment0096355Field003Chars00 ++ (fragment0096355Field004Chars00 ++ (tail)))) fragment0096355Acc00300 := object_fragment0096355_field_002 fuel (fragment0096355Field003Chars00 ++ (fragment0096355Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 14) (SourceJson.white (fragment0096355Field004Chars00 ++ (tail))) fragment0096355Acc00400 := object_fragment0096355_field_003 fuel (fragment0096355Field004Chars00 ++ (tail))
    _ = .ok (fragment0096355Value, tail) := object_fragment0096355_field_004 fuel (tail)

noncomputable def fragment0097435Acc00000 : List SourceJson := []

noncomputable def fragment0097435Chunk000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0097435Chunk000Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '7'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '5'])]) :: (acc))

theorem array_fragment0097435_chunk_000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 17) (SourceJson.white (fragment0097435Chunk000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 15) (SourceJson.white tail) (fragment0097435Chunk000Push00 acc) := by
  rfl

noncomputable def fragment0097435Acc00100 : List SourceJson := fragment0097435Chunk000Push00 fragment0097435Acc00000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0097435_array_chunk_000"
  err.flush

noncomputable def fragment0097435Chunk001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0097435Chunk001Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['4']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '5']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '7'])]) :: (acc))

theorem array_fragment0097435_chunk_001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 15) (SourceJson.white (fragment0097435Chunk001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 13) (SourceJson.white tail) (fragment0097435Chunk001Push00 acc) := by
  rfl

noncomputable def fragment0097435Acc00200 : List SourceJson := fragment0097435Chunk001Push00 fragment0097435Acc00100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0097435_array_chunk_001"
  err.flush

noncomputable def fragment0097435Chunk002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0097435Chunk002Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '5']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '7'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['8']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '5']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '7'])]) :: (acc))

theorem array_fragment0097435_chunk_002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 13) (SourceJson.white (fragment0097435Chunk002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 11) (SourceJson.white tail) (fragment0097435Chunk002Push00 acc) := by
  rfl

noncomputable def fragment0097435Acc00300 : List SourceJson := fragment0097435Chunk002Push00 fragment0097435Acc00200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0097435_array_chunk_002"
  err.flush

noncomputable def fragment0097435Chunk003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']']
noncomputable def fragment0097435Chunk003Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '5']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '7'])]) :: (acc)

theorem array_fragment0097435_chunk_003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 11) (SourceJson.white (fragment0097435Chunk003Chars00 ++ tail)) acc =
      .ok (.arr ((fragment0097435Chunk003Push00 acc).reverse), tail) := by
  rfl

noncomputable def fragment0097435Acc00400 : List SourceJson := fragment0097435Chunk003Push00 fragment0097435Acc00300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0097435_array_chunk_003"
  err.flush

noncomputable def fragment0097435Chars : List Char := '[' :: (fragment0097435Chunk000Chars00 ++ fragment0097435Chunk001Chars00 ++ fragment0097435Chunk002Chars00 ++ fragment0097435Chunk003Chars00)
noncomputable def fragment0097435Value : SourceJson := .arr (fragment0097435Acc00400.reverse)

theorem value_fragment0097435 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 18) (fragment0097435Chars ++ tail) =
      .ok (fragment0097435Value, tail) := by
  have hinput : fragment0097435Chars ++ tail = '[' :: (fragment0097435Chunk000Chars00 ++ (fragment0097435Chunk001Chars00 ++ (fragment0097435Chunk002Chars00 ++ (fragment0097435Chunk003Chars00 ++ (tail))))) := by
    simp only [fragment0097435Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 18) (fragment0097435Chars ++ tail) =
        SourceJson.value (fuel + 18) ('[' :: (fragment0097435Chunk000Chars00 ++ (fragment0097435Chunk001Chars00 ++ (fragment0097435Chunk002Chars00 ++ (fragment0097435Chunk003Chars00 ++ (tail)))))) :=
      congrArg (SourceJson.value (fuel + 18)) hinput
    _ = SourceJson.array (fuel + 17) (SourceJson.white (fragment0097435Chunk000Chars00 ++ (fragment0097435Chunk001Chars00 ++ (fragment0097435Chunk002Chars00 ++ (fragment0097435Chunk003Chars00 ++ (tail)))))) fragment0097435Acc00000 := by rfl
    _ = SourceJson.array (fuel + 15) (SourceJson.white (fragment0097435Chunk001Chars00 ++ (fragment0097435Chunk002Chars00 ++ (fragment0097435Chunk003Chars00 ++ (tail))))) fragment0097435Acc00100 := array_fragment0097435_chunk_000 fuel (fragment0097435Chunk001Chars00 ++ (fragment0097435Chunk002Chars00 ++ (fragment0097435Chunk003Chars00 ++ (tail)))) fragment0097435Acc00000
    _ = SourceJson.array (fuel + 13) (SourceJson.white (fragment0097435Chunk002Chars00 ++ (fragment0097435Chunk003Chars00 ++ (tail)))) fragment0097435Acc00200 := array_fragment0097435_chunk_001 fuel (fragment0097435Chunk002Chars00 ++ (fragment0097435Chunk003Chars00 ++ (tail))) fragment0097435Acc00100
    _ = SourceJson.array (fuel + 11) (SourceJson.white (fragment0097435Chunk003Chars00 ++ (tail))) fragment0097435Acc00300 := array_fragment0097435_chunk_002 fuel (fragment0097435Chunk003Chars00 ++ (tail)) fragment0097435Acc00200
    _ = .ok (fragment0097435Value, tail) := array_fragment0097435_chunk_003 fuel (tail) fragment0097435Acc00300

noncomputable def fragment0097188Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0097188Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0097188Field000Value00 : SourceJson := .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '5']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '7'])]
noncomputable def fragment0097188Acc00100 : List (String × SourceJson) := (fragment0097188Field000Key00, fragment0097188Field000Value00) :: fragment0097188Acc00000
noncomputable def fragment0097188Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0097188_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 22) (SourceJson.white (fragment0097188Field000Chars00 ++ tail)) fragment0097188Acc00000 =
      SourceJson.object (fuel + 21) (SourceJson.white tail) fragment0097188Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0097188_object_field_000"
  err.flush

noncomputable def fragment0097188Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0097188Field001Value00 : SourceJson := .number (String.ofList ['5'])
noncomputable def fragment0097188Acc00200 : List (String × SourceJson) := (fragment0097188Field001Key00, fragment0097188Field001Value00) :: fragment0097188Acc00100
noncomputable def fragment0097188Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '5', ',']

theorem object_fragment0097188_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 21) (SourceJson.white (fragment0097188Field001Chars00 ++ tail)) fragment0097188Acc00100 =
      SourceJson.object (fuel + 20) (SourceJson.white tail) fragment0097188Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0097188_object_field_001"
  err.flush

noncomputable def fragment0097188Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0097188Field002Value00 : SourceJson := .number (String.ofList ['2', '7'])
noncomputable def fragment0097188Acc00300 : List (String × SourceJson) := (fragment0097188Field002Key00, fragment0097188Field002Value00) :: fragment0097188Acc00200
noncomputable def fragment0097188Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '2', '7', ',']

theorem object_fragment0097188_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 20) (SourceJson.white (fragment0097188Field002Chars00 ++ tail)) fragment0097188Acc00200 =
      SourceJson.object (fuel + 19) (SourceJson.white tail) fragment0097188Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0097188_object_field_002"
  err.flush

noncomputable def fragment0097188Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0097188Field003Value00 : SourceJson := fragment0097435Value
noncomputable def fragment0097188Acc00400 : List (String × SourceJson) := (fragment0097188Field003Key00, fragment0097188Field003Value00) :: fragment0097188Acc00300
noncomputable def fragment0097188Field003HeaderChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ']
noncomputable def fragment0097188Field003SuffixChars00 : List Char := [',']
noncomputable def fragment0097188Field003Chars00 : List Char := fragment0097188Field003HeaderChars00 ++ fragment0097435Chars ++ fragment0097188Field003SuffixChars00

noncomputable def fragment0097188Field003AfterValue00 (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending => .ok (.obj (((fragment0097188Field003Key00, result.1) :: fragment0097188Acc00300).reverse), ending)
  | ',' :: ending => SourceJson.object fuel (SourceJson.white ending) ((fragment0097188Field003Key00, result.1) :: fragment0097188Acc00300)
  | _ => .error "object separator missing"

theorem object_fragment0097188_field_003_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 19) (SourceJson.white (fragment0097188Field003HeaderChars00 ++ rest)) fragment0097188Acc00300 =
      (SourceJson.value (fuel + 18) rest).bind (fragment0097188Field003AfterValue00 (fuel + 18)) := by rfl

theorem object_fragment0097188_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 19) (SourceJson.white (fragment0097188Field003Chars00 ++ tail)) fragment0097188Acc00300 =
      SourceJson.object (fuel + 18) (SourceJson.white tail) fragment0097188Acc00400 := by
  have hinput : fragment0097188Field003Chars00 ++ tail = fragment0097188Field003HeaderChars00 ++ (fragment0097435Chars ++ (fragment0097188Field003SuffixChars00 ++ tail)) := by
    simp only [fragment0097188Field003Chars00, List.append_assoc]
  calc
    SourceJson.object (fuel + 19) (SourceJson.white (fragment0097188Field003Chars00 ++ tail)) fragment0097188Acc00300 =
        SourceJson.object (fuel + 19)
          (SourceJson.white (fragment0097188Field003HeaderChars00 ++ (fragment0097435Chars ++ (fragment0097188Field003SuffixChars00 ++ tail)))) fragment0097188Acc00300 :=
      congrArg (fun s => SourceJson.object (fuel + 19) (SourceJson.white s) fragment0097188Acc00300) hinput
    _ = (SourceJson.value (fuel + 18) (fragment0097435Chars ++ (fragment0097188Field003SuffixChars00 ++ tail))).bind
        (fragment0097188Field003AfterValue00 (fuel + 18)) := object_fragment0097188_field_003_header fuel (fragment0097435Chars ++ (fragment0097188Field003SuffixChars00 ++ tail))
    _ = (Except.ok (fragment0097435Value, fragment0097188Field003SuffixChars00 ++ tail)).bind (fragment0097188Field003AfterValue00 (fuel + 18)) :=
      congrArg (fun result => result.bind (fragment0097188Field003AfterValue00 (fuel + 18)))
        (value_fragment0097435 (fuel + 0) (fragment0097188Field003SuffixChars00 ++ tail))
    _ = SourceJson.object (fuel + 18) (SourceJson.white tail) fragment0097188Acc00400 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0097188_object_field_003"
  err.flush

noncomputable def fragment0097188Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0097188Field004Value00 : SourceJson := .number (String.ofList ['1', '0'])
noncomputable def fragment0097188Acc00500 : List (String × SourceJson) := (fragment0097188Field004Key00, fragment0097188Field004Value00) :: fragment0097188Acc00400
noncomputable def fragment0097188Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '0', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0097188_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 18) (SourceJson.white (fragment0097188Field004Chars00 ++ tail)) fragment0097188Acc00400 =
      .ok (.obj (fragment0097188Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0097188_object_field_004"
  err.flush

noncomputable def fragment0097188Chars : List Char := '{' :: (fragment0097188Field000Chars00 ++ fragment0097188Field001Chars00 ++ fragment0097188Field002Chars00 ++ fragment0097188Field003Chars00 ++ fragment0097188Field004Chars00)
noncomputable def fragment0097188Value : SourceJson := .obj (fragment0097188Acc00500.reverse)

theorem value_fragment0097188 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 23) (fragment0097188Chars ++ tail) =
      .ok (fragment0097188Value, tail) := by
  have hinput : fragment0097188Chars ++ tail = '{' :: (fragment0097188Field000Chars00 ++ (fragment0097188Field001Chars00 ++ (fragment0097188Field002Chars00 ++ (fragment0097188Field003Chars00 ++ (fragment0097188Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0097188Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 23) (fragment0097188Chars ++ tail) =
        SourceJson.value (fuel + 23) ('{' :: (fragment0097188Field000Chars00 ++ (fragment0097188Field001Chars00 ++ (fragment0097188Field002Chars00 ++ (fragment0097188Field003Chars00 ++ (fragment0097188Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 23)) hinput
    _ = SourceJson.object (fuel + 22) (SourceJson.white (fragment0097188Field000Chars00 ++ (fragment0097188Field001Chars00 ++ (fragment0097188Field002Chars00 ++ (fragment0097188Field003Chars00 ++ (fragment0097188Field004Chars00 ++ (tail))))))) fragment0097188Acc00000 := by rfl
    _ = SourceJson.object (fuel + 21) (SourceJson.white (fragment0097188Field001Chars00 ++ (fragment0097188Field002Chars00 ++ (fragment0097188Field003Chars00 ++ (fragment0097188Field004Chars00 ++ (tail)))))) fragment0097188Acc00100 := object_fragment0097188_field_000 fuel (fragment0097188Field001Chars00 ++ (fragment0097188Field002Chars00 ++ (fragment0097188Field003Chars00 ++ (fragment0097188Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 20) (SourceJson.white (fragment0097188Field002Chars00 ++ (fragment0097188Field003Chars00 ++ (fragment0097188Field004Chars00 ++ (tail))))) fragment0097188Acc00200 := object_fragment0097188_field_001 fuel (fragment0097188Field002Chars00 ++ (fragment0097188Field003Chars00 ++ (fragment0097188Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 19) (SourceJson.white (fragment0097188Field003Chars00 ++ (fragment0097188Field004Chars00 ++ (tail)))) fragment0097188Acc00300 := object_fragment0097188_field_002 fuel (fragment0097188Field003Chars00 ++ (fragment0097188Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 18) (SourceJson.white (fragment0097188Field004Chars00 ++ (tail))) fragment0097188Acc00400 := object_fragment0097188_field_003 fuel (fragment0097188Field004Chars00 ++ (tail))
    _ = .ok (fragment0097188Value, tail) := object_fragment0097188_field_004 fuel (tail)

noncomputable def fragment0099606Acc00000 : List SourceJson := []

noncomputable def fragment0099606Chunk000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0099606Chunk000Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['9']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4'])]) :: (acc))

theorem array_fragment0099606_chunk_000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 22) (SourceJson.white (fragment0099606Chunk000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 20) (SourceJson.white tail) (fragment0099606Chunk000Push00 acc) := by
  rfl

noncomputable def fragment0099606Acc00100 : List SourceJson := fragment0099606Chunk000Push00 fragment0099606Acc00000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0099606_array_chunk_000"
  err.flush

noncomputable def fragment0099606Chunk001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0099606Chunk001Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['4']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6'])]) :: (acc))

theorem array_fragment0099606_chunk_001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 20) (SourceJson.white (fragment0099606Chunk001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 18) (SourceJson.white tail) (fragment0099606Chunk001Push00 acc) := by
  rfl

noncomputable def fragment0099606Acc00200 : List SourceJson := fragment0099606Chunk001Push00 fragment0099606Acc00100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0099606_array_chunk_001"
  err.flush

noncomputable def fragment0099606Chunk002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0099606Chunk002Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['7']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '6'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5'])]) :: (acc))

theorem array_fragment0099606_chunk_002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 18) (SourceJson.white (fragment0099606Chunk002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 16) (SourceJson.white tail) (fragment0099606Chunk002Push00 acc) := by
  rfl

noncomputable def fragment0099606Acc00300 : List SourceJson := fragment0099606Chunk002Push00 fragment0099606Acc00200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0099606_array_chunk_002"
  err.flush

noncomputable def fragment0099606Chunk003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']']
noncomputable def fragment0099606Chunk003Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6'])]) :: ((.arr [.number (String.ofList ['7']), .number (String.ofList ['9']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '4']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6'])]) :: (acc))

theorem array_fragment0099606_chunk_003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 16) (SourceJson.white (fragment0099606Chunk003Chars00 ++ tail)) acc =
      .ok (.arr ((fragment0099606Chunk003Push00 acc).reverse), tail) := by
  rfl

noncomputable def fragment0099606Acc00400 : List SourceJson := fragment0099606Chunk003Push00 fragment0099606Acc00300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0099606_array_chunk_003"
  err.flush

noncomputable def fragment0099606Chars : List Char := '[' :: (fragment0099606Chunk000Chars00 ++ fragment0099606Chunk001Chars00 ++ fragment0099606Chunk002Chars00 ++ fragment0099606Chunk003Chars00)
noncomputable def fragment0099606Value : SourceJson := .arr (fragment0099606Acc00400.reverse)

theorem value_fragment0099606 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 23) (fragment0099606Chars ++ tail) =
      .ok (fragment0099606Value, tail) := by
  have hinput : fragment0099606Chars ++ tail = '[' :: (fragment0099606Chunk000Chars00 ++ (fragment0099606Chunk001Chars00 ++ (fragment0099606Chunk002Chars00 ++ (fragment0099606Chunk003Chars00 ++ (tail))))) := by
    simp only [fragment0099606Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 23) (fragment0099606Chars ++ tail) =
        SourceJson.value (fuel + 23) ('[' :: (fragment0099606Chunk000Chars00 ++ (fragment0099606Chunk001Chars00 ++ (fragment0099606Chunk002Chars00 ++ (fragment0099606Chunk003Chars00 ++ (tail)))))) :=
      congrArg (SourceJson.value (fuel + 23)) hinput
    _ = SourceJson.array (fuel + 22) (SourceJson.white (fragment0099606Chunk000Chars00 ++ (fragment0099606Chunk001Chars00 ++ (fragment0099606Chunk002Chars00 ++ (fragment0099606Chunk003Chars00 ++ (tail)))))) fragment0099606Acc00000 := by rfl
    _ = SourceJson.array (fuel + 20) (SourceJson.white (fragment0099606Chunk001Chars00 ++ (fragment0099606Chunk002Chars00 ++ (fragment0099606Chunk003Chars00 ++ (tail))))) fragment0099606Acc00100 := array_fragment0099606_chunk_000 fuel (fragment0099606Chunk001Chars00 ++ (fragment0099606Chunk002Chars00 ++ (fragment0099606Chunk003Chars00 ++ (tail)))) fragment0099606Acc00000
    _ = SourceJson.array (fuel + 18) (SourceJson.white (fragment0099606Chunk002Chars00 ++ (fragment0099606Chunk003Chars00 ++ (tail)))) fragment0099606Acc00200 := array_fragment0099606_chunk_001 fuel (fragment0099606Chunk002Chars00 ++ (fragment0099606Chunk003Chars00 ++ (tail))) fragment0099606Acc00100
    _ = SourceJson.array (fuel + 16) (SourceJson.white (fragment0099606Chunk003Chars00 ++ (tail))) fragment0099606Acc00300 := array_fragment0099606_chunk_002 fuel (fragment0099606Chunk003Chars00 ++ (tail)) fragment0099606Acc00200
    _ = .ok (fragment0099606Value, tail) := array_fragment0099606_chunk_003 fuel (tail) fragment0099606Acc00300

noncomputable def fragment0099283Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0099283Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0099283Field000Value00 : SourceJson := .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6'])]
noncomputable def fragment0099283Acc00100 : List (String × SourceJson) := (fragment0099283Field000Key00, fragment0099283Field000Value00) :: fragment0099283Acc00000
noncomputable def fragment0099283Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0099283_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 27) (SourceJson.white (fragment0099283Field000Chars00 ++ tail)) fragment0099283Acc00000 =
      SourceJson.object (fuel + 26) (SourceJson.white tail) fragment0099283Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0099283_object_field_000"
  err.flush

noncomputable def fragment0099283Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0099283Field001Value00 : SourceJson := .number (String.ofList ['5'])
noncomputable def fragment0099283Acc00200 : List (String × SourceJson) := (fragment0099283Field001Key00, fragment0099283Field001Value00) :: fragment0099283Acc00100
noncomputable def fragment0099283Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '5', ',']

theorem object_fragment0099283_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 26) (SourceJson.white (fragment0099283Field001Chars00 ++ tail)) fragment0099283Acc00100 =
      SourceJson.object (fuel + 25) (SourceJson.white tail) fragment0099283Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0099283_object_field_001"
  err.flush

noncomputable def fragment0099283Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0099283Field002Value00 : SourceJson := .number (String.ofList ['2', '6'])
noncomputable def fragment0099283Acc00300 : List (String × SourceJson) := (fragment0099283Field002Key00, fragment0099283Field002Value00) :: fragment0099283Acc00200
noncomputable def fragment0099283Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '2', '6', ',']

theorem object_fragment0099283_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 25) (SourceJson.white (fragment0099283Field002Chars00 ++ tail)) fragment0099283Acc00200 =
      SourceJson.object (fuel + 24) (SourceJson.white tail) fragment0099283Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0099283_object_field_002"
  err.flush

noncomputable def fragment0099283Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0099283Field003Value00 : SourceJson := fragment0099606Value
noncomputable def fragment0099283Acc00400 : List (String × SourceJson) := (fragment0099283Field003Key00, fragment0099283Field003Value00) :: fragment0099283Acc00300
noncomputable def fragment0099283Field003HeaderChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ']
noncomputable def fragment0099283Field003SuffixChars00 : List Char := [',']
noncomputable def fragment0099283Field003Chars00 : List Char := fragment0099283Field003HeaderChars00 ++ fragment0099606Chars ++ fragment0099283Field003SuffixChars00

noncomputable def fragment0099283Field003AfterValue00 (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending => .ok (.obj (((fragment0099283Field003Key00, result.1) :: fragment0099283Acc00300).reverse), ending)
  | ',' :: ending => SourceJson.object fuel (SourceJson.white ending) ((fragment0099283Field003Key00, result.1) :: fragment0099283Acc00300)
  | _ => .error "object separator missing"

theorem object_fragment0099283_field_003_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 24) (SourceJson.white (fragment0099283Field003HeaderChars00 ++ rest)) fragment0099283Acc00300 =
      (SourceJson.value (fuel + 23) rest).bind (fragment0099283Field003AfterValue00 (fuel + 23)) := by rfl

theorem object_fragment0099283_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 24) (SourceJson.white (fragment0099283Field003Chars00 ++ tail)) fragment0099283Acc00300 =
      SourceJson.object (fuel + 23) (SourceJson.white tail) fragment0099283Acc00400 := by
  have hinput : fragment0099283Field003Chars00 ++ tail = fragment0099283Field003HeaderChars00 ++ (fragment0099606Chars ++ (fragment0099283Field003SuffixChars00 ++ tail)) := by
    simp only [fragment0099283Field003Chars00, List.append_assoc]
  calc
    SourceJson.object (fuel + 24) (SourceJson.white (fragment0099283Field003Chars00 ++ tail)) fragment0099283Acc00300 =
        SourceJson.object (fuel + 24)
          (SourceJson.white (fragment0099283Field003HeaderChars00 ++ (fragment0099606Chars ++ (fragment0099283Field003SuffixChars00 ++ tail)))) fragment0099283Acc00300 :=
      congrArg (fun s => SourceJson.object (fuel + 24) (SourceJson.white s) fragment0099283Acc00300) hinput
    _ = (SourceJson.value (fuel + 23) (fragment0099606Chars ++ (fragment0099283Field003SuffixChars00 ++ tail))).bind
        (fragment0099283Field003AfterValue00 (fuel + 23)) := object_fragment0099283_field_003_header fuel (fragment0099606Chars ++ (fragment0099283Field003SuffixChars00 ++ tail))
    _ = (Except.ok (fragment0099606Value, fragment0099283Field003SuffixChars00 ++ tail)).bind (fragment0099283Field003AfterValue00 (fuel + 23)) :=
      congrArg (fun result => result.bind (fragment0099283Field003AfterValue00 (fuel + 23)))
        (value_fragment0099606 (fuel + 0) (fragment0099283Field003SuffixChars00 ++ tail))
    _ = SourceJson.object (fuel + 23) (SourceJson.white tail) fragment0099283Acc00400 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0099283_object_field_003"
  err.flush

noncomputable def fragment0099283Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0099283Field004Value00 : SourceJson := .number (String.ofList ['3', '0'])
noncomputable def fragment0099283Acc00500 : List (String × SourceJson) := (fragment0099283Field004Key00, fragment0099283Field004Value00) :: fragment0099283Acc00400
noncomputable def fragment0099283Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '3', '0', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0099283_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 23) (SourceJson.white (fragment0099283Field004Chars00 ++ tail)) fragment0099283Acc00400 =
      .ok (.obj (fragment0099283Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0099283_object_field_004"
  err.flush

noncomputable def fragment0099283Chars : List Char := '{' :: (fragment0099283Field000Chars00 ++ fragment0099283Field001Chars00 ++ fragment0099283Field002Chars00 ++ fragment0099283Field003Chars00 ++ fragment0099283Field004Chars00)
noncomputable def fragment0099283Value : SourceJson := .obj (fragment0099283Acc00500.reverse)

theorem value_fragment0099283 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 28) (fragment0099283Chars ++ tail) =
      .ok (fragment0099283Value, tail) := by
  have hinput : fragment0099283Chars ++ tail = '{' :: (fragment0099283Field000Chars00 ++ (fragment0099283Field001Chars00 ++ (fragment0099283Field002Chars00 ++ (fragment0099283Field003Chars00 ++ (fragment0099283Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0099283Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 28) (fragment0099283Chars ++ tail) =
        SourceJson.value (fuel + 28) ('{' :: (fragment0099283Field000Chars00 ++ (fragment0099283Field001Chars00 ++ (fragment0099283Field002Chars00 ++ (fragment0099283Field003Chars00 ++ (fragment0099283Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 28)) hinput
    _ = SourceJson.object (fuel + 27) (SourceJson.white (fragment0099283Field000Chars00 ++ (fragment0099283Field001Chars00 ++ (fragment0099283Field002Chars00 ++ (fragment0099283Field003Chars00 ++ (fragment0099283Field004Chars00 ++ (tail))))))) fragment0099283Acc00000 := by rfl
    _ = SourceJson.object (fuel + 26) (SourceJson.white (fragment0099283Field001Chars00 ++ (fragment0099283Field002Chars00 ++ (fragment0099283Field003Chars00 ++ (fragment0099283Field004Chars00 ++ (tail)))))) fragment0099283Acc00100 := object_fragment0099283_field_000 fuel (fragment0099283Field001Chars00 ++ (fragment0099283Field002Chars00 ++ (fragment0099283Field003Chars00 ++ (fragment0099283Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 25) (SourceJson.white (fragment0099283Field002Chars00 ++ (fragment0099283Field003Chars00 ++ (fragment0099283Field004Chars00 ++ (tail))))) fragment0099283Acc00200 := object_fragment0099283_field_001 fuel (fragment0099283Field002Chars00 ++ (fragment0099283Field003Chars00 ++ (fragment0099283Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 24) (SourceJson.white (fragment0099283Field003Chars00 ++ (fragment0099283Field004Chars00 ++ (tail)))) fragment0099283Acc00300 := object_fragment0099283_field_002 fuel (fragment0099283Field003Chars00 ++ (fragment0099283Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 23) (SourceJson.white (fragment0099283Field004Chars00 ++ (tail))) fragment0099283Acc00400 := object_fragment0099283_field_003 fuel (fragment0099283Field004Chars00 ++ (tail))
    _ = .ok (fragment0099283Value, tail) := object_fragment0099283_field_004 fuel (tail)

noncomputable def fragment0101377Acc00000 : List SourceJson := []

noncomputable def fragment0101377Chunk000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0101377Chunk000Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['4'])]) :: (acc))

theorem array_fragment0101377_chunk_000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 15) (SourceJson.white (fragment0101377Chunk000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 13) (SourceJson.white tail) (fragment0101377Chunk000Push00 acc) := by
  rfl

noncomputable def fragment0101377Acc00100 : List SourceJson := fragment0101377Chunk000Push00 fragment0101377Acc00000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0101377_array_chunk_000"
  err.flush

noncomputable def fragment0101377Chunk001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0101377Chunk001Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['4']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '3'])]) :: (acc))

theorem array_fragment0101377_chunk_001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 13) (SourceJson.white (fragment0101377Chunk001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 11) (SourceJson.white tail) (fragment0101377Chunk001Push00 acc) := by
  rfl

noncomputable def fragment0101377Acc00200 : List SourceJson := fragment0101377Chunk001Push00 fragment0101377Acc00100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0101377_array_chunk_001"
  err.flush

noncomputable def fragment0101377Chunk002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0101377Chunk002Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['7']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '4'])]) :: ((.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['7']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4'])]) :: (acc))

theorem array_fragment0101377_chunk_002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 11) (SourceJson.white (fragment0101377Chunk002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 9) (SourceJson.white tail) (fragment0101377Chunk002Push00 acc) := by
  rfl

noncomputable def fragment0101377Acc00300 : List SourceJson := fragment0101377Chunk002Push00 fragment0101377Acc00200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0101377_array_chunk_002"
  err.flush

noncomputable def fragment0101377Chunk003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']']
noncomputable def fragment0101377Chunk003Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4'])]) :: (acc)

theorem array_fragment0101377_chunk_003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 9) (SourceJson.white (fragment0101377Chunk003Chars00 ++ tail)) acc =
      .ok (.arr ((fragment0101377Chunk003Push00 acc).reverse), tail) := by
  rfl

noncomputable def fragment0101377Acc00400 : List SourceJson := fragment0101377Chunk003Push00 fragment0101377Acc00300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0101377_array_chunk_003"
  err.flush

noncomputable def fragment0101377Chars : List Char := '[' :: (fragment0101377Chunk000Chars00 ++ fragment0101377Chunk001Chars00 ++ fragment0101377Chunk002Chars00 ++ fragment0101377Chunk003Chars00)
noncomputable def fragment0101377Value : SourceJson := .arr (fragment0101377Acc00400.reverse)

theorem value_fragment0101377 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 16) (fragment0101377Chars ++ tail) =
      .ok (fragment0101377Value, tail) := by
  have hinput : fragment0101377Chars ++ tail = '[' :: (fragment0101377Chunk000Chars00 ++ (fragment0101377Chunk001Chars00 ++ (fragment0101377Chunk002Chars00 ++ (fragment0101377Chunk003Chars00 ++ (tail))))) := by
    simp only [fragment0101377Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 16) (fragment0101377Chars ++ tail) =
        SourceJson.value (fuel + 16) ('[' :: (fragment0101377Chunk000Chars00 ++ (fragment0101377Chunk001Chars00 ++ (fragment0101377Chunk002Chars00 ++ (fragment0101377Chunk003Chars00 ++ (tail)))))) :=
      congrArg (SourceJson.value (fuel + 16)) hinput
    _ = SourceJson.array (fuel + 15) (SourceJson.white (fragment0101377Chunk000Chars00 ++ (fragment0101377Chunk001Chars00 ++ (fragment0101377Chunk002Chars00 ++ (fragment0101377Chunk003Chars00 ++ (tail)))))) fragment0101377Acc00000 := by rfl
    _ = SourceJson.array (fuel + 13) (SourceJson.white (fragment0101377Chunk001Chars00 ++ (fragment0101377Chunk002Chars00 ++ (fragment0101377Chunk003Chars00 ++ (tail))))) fragment0101377Acc00100 := array_fragment0101377_chunk_000 fuel (fragment0101377Chunk001Chars00 ++ (fragment0101377Chunk002Chars00 ++ (fragment0101377Chunk003Chars00 ++ (tail)))) fragment0101377Acc00000
    _ = SourceJson.array (fuel + 11) (SourceJson.white (fragment0101377Chunk002Chars00 ++ (fragment0101377Chunk003Chars00 ++ (tail)))) fragment0101377Acc00200 := array_fragment0101377_chunk_001 fuel (fragment0101377Chunk002Chars00 ++ (fragment0101377Chunk003Chars00 ++ (tail))) fragment0101377Acc00100
    _ = SourceJson.array (fuel + 9) (SourceJson.white (fragment0101377Chunk003Chars00 ++ (tail))) fragment0101377Acc00300 := array_fragment0101377_chunk_002 fuel (fragment0101377Chunk003Chars00 ++ (tail)) fragment0101377Acc00200
    _ = .ok (fragment0101377Value, tail) := array_fragment0101377_chunk_003 fuel (tail) fragment0101377Acc00300

noncomputable def fragment0101144Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0101144Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0101144Field000Value00 : SourceJson := .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4'])]
noncomputable def fragment0101144Acc00100 : List (String × SourceJson) := (fragment0101144Field000Key00, fragment0101144Field000Value00) :: fragment0101144Acc00000
noncomputable def fragment0101144Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0101144_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 20) (SourceJson.white (fragment0101144Field000Chars00 ++ tail)) fragment0101144Acc00000 =
      SourceJson.object (fuel + 19) (SourceJson.white tail) fragment0101144Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0101144_object_field_000"
  err.flush

noncomputable def fragment0101144Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0101144Field001Value00 : SourceJson := .number (String.ofList ['4'])
noncomputable def fragment0101144Acc00200 : List (String × SourceJson) := (fragment0101144Field001Key00, fragment0101144Field001Value00) :: fragment0101144Acc00100
noncomputable def fragment0101144Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '4', ',']

theorem object_fragment0101144_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 19) (SourceJson.white (fragment0101144Field001Chars00 ++ tail)) fragment0101144Acc00100 =
      SourceJson.object (fuel + 18) (SourceJson.white tail) fragment0101144Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0101144_object_field_001"
  err.flush

noncomputable def fragment0101144Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0101144Field002Value00 : SourceJson := .number (String.ofList ['1', '4'])
noncomputable def fragment0101144Acc00300 : List (String × SourceJson) := (fragment0101144Field002Key00, fragment0101144Field002Value00) :: fragment0101144Acc00200
noncomputable def fragment0101144Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '1', '4', ',']

theorem object_fragment0101144_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 18) (SourceJson.white (fragment0101144Field002Chars00 ++ tail)) fragment0101144Acc00200 =
      SourceJson.object (fuel + 17) (SourceJson.white tail) fragment0101144Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0101144_object_field_002"
  err.flush

noncomputable def fragment0101144Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0101144Field003Value00 : SourceJson := fragment0101377Value
noncomputable def fragment0101144Acc00400 : List (String × SourceJson) := (fragment0101144Field003Key00, fragment0101144Field003Value00) :: fragment0101144Acc00300
noncomputable def fragment0101144Field003HeaderChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ']
noncomputable def fragment0101144Field003SuffixChars00 : List Char := [',']
noncomputable def fragment0101144Field003Chars00 : List Char := fragment0101144Field003HeaderChars00 ++ fragment0101377Chars ++ fragment0101144Field003SuffixChars00

noncomputable def fragment0101144Field003AfterValue00 (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending => .ok (.obj (((fragment0101144Field003Key00, result.1) :: fragment0101144Acc00300).reverse), ending)
  | ',' :: ending => SourceJson.object fuel (SourceJson.white ending) ((fragment0101144Field003Key00, result.1) :: fragment0101144Acc00300)
  | _ => .error "object separator missing"

theorem object_fragment0101144_field_003_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 17) (SourceJson.white (fragment0101144Field003HeaderChars00 ++ rest)) fragment0101144Acc00300 =
      (SourceJson.value (fuel + 16) rest).bind (fragment0101144Field003AfterValue00 (fuel + 16)) := by rfl

theorem object_fragment0101144_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 17) (SourceJson.white (fragment0101144Field003Chars00 ++ tail)) fragment0101144Acc00300 =
      SourceJson.object (fuel + 16) (SourceJson.white tail) fragment0101144Acc00400 := by
  have hinput : fragment0101144Field003Chars00 ++ tail = fragment0101144Field003HeaderChars00 ++ (fragment0101377Chars ++ (fragment0101144Field003SuffixChars00 ++ tail)) := by
    simp only [fragment0101144Field003Chars00, List.append_assoc]
  calc
    SourceJson.object (fuel + 17) (SourceJson.white (fragment0101144Field003Chars00 ++ tail)) fragment0101144Acc00300 =
        SourceJson.object (fuel + 17)
          (SourceJson.white (fragment0101144Field003HeaderChars00 ++ (fragment0101377Chars ++ (fragment0101144Field003SuffixChars00 ++ tail)))) fragment0101144Acc00300 :=
      congrArg (fun s => SourceJson.object (fuel + 17) (SourceJson.white s) fragment0101144Acc00300) hinput
    _ = (SourceJson.value (fuel + 16) (fragment0101377Chars ++ (fragment0101144Field003SuffixChars00 ++ tail))).bind
        (fragment0101144Field003AfterValue00 (fuel + 16)) := object_fragment0101144_field_003_header fuel (fragment0101377Chars ++ (fragment0101144Field003SuffixChars00 ++ tail))
    _ = (Except.ok (fragment0101377Value, fragment0101144Field003SuffixChars00 ++ tail)).bind (fragment0101144Field003AfterValue00 (fuel + 16)) :=
      congrArg (fun result => result.bind (fragment0101144Field003AfterValue00 (fuel + 16)))
        (value_fragment0101377 (fuel + 0) (fragment0101144Field003SuffixChars00 ++ tail))
    _ = SourceJson.object (fuel + 16) (SourceJson.white tail) fragment0101144Acc00400 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0101144_object_field_003"
  err.flush

noncomputable def fragment0101144Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0101144Field004Value00 : SourceJson := .number (String.ofList ['1', '0'])
noncomputable def fragment0101144Acc00500 : List (String × SourceJson) := (fragment0101144Field004Key00, fragment0101144Field004Value00) :: fragment0101144Acc00400
noncomputable def fragment0101144Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '0', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0101144_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 16) (SourceJson.white (fragment0101144Field004Chars00 ++ tail)) fragment0101144Acc00400 =
      .ok (.obj (fragment0101144Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0101144_object_field_004"
  err.flush

noncomputable def fragment0101144Chars : List Char := '{' :: (fragment0101144Field000Chars00 ++ fragment0101144Field001Chars00 ++ fragment0101144Field002Chars00 ++ fragment0101144Field003Chars00 ++ fragment0101144Field004Chars00)
noncomputable def fragment0101144Value : SourceJson := .obj (fragment0101144Acc00500.reverse)

theorem value_fragment0101144 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 21) (fragment0101144Chars ++ tail) =
      .ok (fragment0101144Value, tail) := by
  have hinput : fragment0101144Chars ++ tail = '{' :: (fragment0101144Field000Chars00 ++ (fragment0101144Field001Chars00 ++ (fragment0101144Field002Chars00 ++ (fragment0101144Field003Chars00 ++ (fragment0101144Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0101144Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 21) (fragment0101144Chars ++ tail) =
        SourceJson.value (fuel + 21) ('{' :: (fragment0101144Field000Chars00 ++ (fragment0101144Field001Chars00 ++ (fragment0101144Field002Chars00 ++ (fragment0101144Field003Chars00 ++ (fragment0101144Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 21)) hinput
    _ = SourceJson.object (fuel + 20) (SourceJson.white (fragment0101144Field000Chars00 ++ (fragment0101144Field001Chars00 ++ (fragment0101144Field002Chars00 ++ (fragment0101144Field003Chars00 ++ (fragment0101144Field004Chars00 ++ (tail))))))) fragment0101144Acc00000 := by rfl
    _ = SourceJson.object (fuel + 19) (SourceJson.white (fragment0101144Field001Chars00 ++ (fragment0101144Field002Chars00 ++ (fragment0101144Field003Chars00 ++ (fragment0101144Field004Chars00 ++ (tail)))))) fragment0101144Acc00100 := object_fragment0101144_field_000 fuel (fragment0101144Field001Chars00 ++ (fragment0101144Field002Chars00 ++ (fragment0101144Field003Chars00 ++ (fragment0101144Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 18) (SourceJson.white (fragment0101144Field002Chars00 ++ (fragment0101144Field003Chars00 ++ (fragment0101144Field004Chars00 ++ (tail))))) fragment0101144Acc00200 := object_fragment0101144_field_001 fuel (fragment0101144Field002Chars00 ++ (fragment0101144Field003Chars00 ++ (fragment0101144Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 17) (SourceJson.white (fragment0101144Field003Chars00 ++ (fragment0101144Field004Chars00 ++ (tail)))) fragment0101144Acc00300 := object_fragment0101144_field_002 fuel (fragment0101144Field003Chars00 ++ (fragment0101144Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 16) (SourceJson.white (fragment0101144Field004Chars00 ++ (tail))) fragment0101144Acc00400 := object_fragment0101144_field_003 fuel (fragment0101144Field004Chars00 ++ (tail))
    _ = .ok (fragment0101144Value, tail) := object_fragment0101144_field_004 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0016_before_reader"
  err.flush

noncomputable def chunk0016LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0016SuffixChars00 : List Char := [',']
noncomputable def chunk0016Chars00 : List Char := chunk0016LeadChars00 ++ fragment0094533Chars ++ chunk0016SuffixChars00
noncomputable def chunk0016Push00 (acc : List SourceJson) : List SourceJson := fragment0094533Value :: acc

noncomputable def chunk0016AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0016_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 63)
      (SourceJson.white (chunk0016LeadChars00 ++ (fragment0094533Chars ++ rest))) acc =
      (SourceJson.value (fuel + 62) (fragment0094533Chars ++ rest)).bind
        (chunk0016AfterValue00 (fuel + 62) acc) := by rfl

theorem array_chunk0016 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 63) (SourceJson.white (chunk0016Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 62) (SourceJson.white tail) (chunk0016Push00 acc) := by
  have hinput : chunk0016Chars00 ++ tail = chunk0016LeadChars00 ++ (fragment0094533Chars ++ (chunk0016SuffixChars00 ++ tail)) := by
    simp only [chunk0016Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 63) (SourceJson.white (chunk0016Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 63)
          (SourceJson.white (chunk0016LeadChars00 ++ (fragment0094533Chars ++ (chunk0016SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 63) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 62) (fragment0094533Chars ++ (chunk0016SuffixChars00 ++ tail))).bind
        (chunk0016AfterValue00 (fuel + 62) acc) := array_chunk0016_head fuel (chunk0016SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0094533Value, chunk0016SuffixChars00 ++ tail)).bind
        (chunk0016AfterValue00 (fuel + 62) acc) :=
      congrArg (fun result => result.bind (chunk0016AfterValue00 (fuel + 62) acc))
        (value_fragment0094533 (fuel + 35) (chunk0016SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 62) (SourceJson.white tail) (chunk0016Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0016_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0017_before_reader"
  err.flush

noncomputable def chunk0017LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0017SuffixChars00 : List Char := [',']
noncomputable def chunk0017Chars00 : List Char := chunk0017LeadChars00 ++ fragment0096355Chars ++ chunk0017SuffixChars00
noncomputable def chunk0017Push00 (acc : List SourceJson) : List SourceJson := fragment0096355Value :: acc

noncomputable def chunk0017AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0017_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 62)
      (SourceJson.white (chunk0017LeadChars00 ++ (fragment0096355Chars ++ rest))) acc =
      (SourceJson.value (fuel + 61) (fragment0096355Chars ++ rest)).bind
        (chunk0017AfterValue00 (fuel + 61) acc) := by rfl

theorem array_chunk0017 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 62) (SourceJson.white (chunk0017Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 61) (SourceJson.white tail) (chunk0017Push00 acc) := by
  have hinput : chunk0017Chars00 ++ tail = chunk0017LeadChars00 ++ (fragment0096355Chars ++ (chunk0017SuffixChars00 ++ tail)) := by
    simp only [chunk0017Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 62) (SourceJson.white (chunk0017Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 62)
          (SourceJson.white (chunk0017LeadChars00 ++ (fragment0096355Chars ++ (chunk0017SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 62) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 61) (fragment0096355Chars ++ (chunk0017SuffixChars00 ++ tail))).bind
        (chunk0017AfterValue00 (fuel + 61) acc) := array_chunk0017_head fuel (chunk0017SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0096355Value, chunk0017SuffixChars00 ++ tail)).bind
        (chunk0017AfterValue00 (fuel + 61) acc) :=
      congrArg (fun result => result.bind (chunk0017AfterValue00 (fuel + 61) acc))
        (value_fragment0096355 (fuel + 42) (chunk0017SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 61) (SourceJson.white tail) (chunk0017Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0017_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0018_before_reader"
  err.flush

noncomputable def chunk0018LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0018SuffixChars00 : List Char := [',']
noncomputable def chunk0018Chars00 : List Char := chunk0018LeadChars00 ++ fragment0097188Chars ++ chunk0018SuffixChars00
noncomputable def chunk0018Push00 (acc : List SourceJson) : List SourceJson := fragment0097188Value :: acc

noncomputable def chunk0018AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0018_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 61)
      (SourceJson.white (chunk0018LeadChars00 ++ (fragment0097188Chars ++ rest))) acc =
      (SourceJson.value (fuel + 60) (fragment0097188Chars ++ rest)).bind
        (chunk0018AfterValue00 (fuel + 60) acc) := by rfl

theorem array_chunk0018 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 61) (SourceJson.white (chunk0018Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 60) (SourceJson.white tail) (chunk0018Push00 acc) := by
  have hinput : chunk0018Chars00 ++ tail = chunk0018LeadChars00 ++ (fragment0097188Chars ++ (chunk0018SuffixChars00 ++ tail)) := by
    simp only [chunk0018Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 61) (SourceJson.white (chunk0018Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 61)
          (SourceJson.white (chunk0018LeadChars00 ++ (fragment0097188Chars ++ (chunk0018SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 61) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 60) (fragment0097188Chars ++ (chunk0018SuffixChars00 ++ tail))).bind
        (chunk0018AfterValue00 (fuel + 60) acc) := array_chunk0018_head fuel (chunk0018SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0097188Value, chunk0018SuffixChars00 ++ tail)).bind
        (chunk0018AfterValue00 (fuel + 60) acc) :=
      congrArg (fun result => result.bind (chunk0018AfterValue00 (fuel + 60) acc))
        (value_fragment0097188 (fuel + 37) (chunk0018SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 60) (SourceJson.white tail) (chunk0018Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0018_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0019_before_reader"
  err.flush

noncomputable def chunk0019Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0019Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['3'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['2'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['3'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['0']), .number (String.ofList ['1'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['3'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['3'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['1']))]) :: (acc)

theorem array_chunk0019 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 60) (SourceJson.white (chunk0019Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 59) (SourceJson.white tail) (chunk0019Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0019_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0020_before_reader"
  err.flush

noncomputable def chunk0020Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0020Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['4'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['3'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['4'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['3'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['4'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['3']), .number (String.ofList ['4'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['4'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['1']))]) :: (acc)

theorem array_chunk0020 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 59) (SourceJson.white (chunk0020Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 58) (SourceJson.white tail) (chunk0020Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0020_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0021_before_reader"
  err.flush

noncomputable def chunk0021LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0021SuffixChars00 : List Char := [',']
noncomputable def chunk0021Chars00 : List Char := chunk0021LeadChars00 ++ fragment0099283Chars ++ chunk0021SuffixChars00
noncomputable def chunk0021Push00 (acc : List SourceJson) : List SourceJson := fragment0099283Value :: acc

noncomputable def chunk0021AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0021_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 58)
      (SourceJson.white (chunk0021LeadChars00 ++ (fragment0099283Chars ++ rest))) acc =
      (SourceJson.value (fuel + 57) (fragment0099283Chars ++ rest)).bind
        (chunk0021AfterValue00 (fuel + 57) acc) := by rfl

theorem array_chunk0021 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 58) (SourceJson.white (chunk0021Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 57) (SourceJson.white tail) (chunk0021Push00 acc) := by
  have hinput : chunk0021Chars00 ++ tail = chunk0021LeadChars00 ++ (fragment0099283Chars ++ (chunk0021SuffixChars00 ++ tail)) := by
    simp only [chunk0021Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 58) (SourceJson.white (chunk0021Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 58)
          (SourceJson.white (chunk0021LeadChars00 ++ (fragment0099283Chars ++ (chunk0021SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 58) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 57) (fragment0099283Chars ++ (chunk0021SuffixChars00 ++ tail))).bind
        (chunk0021AfterValue00 (fuel + 57) acc) := array_chunk0021_head fuel (chunk0021SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0099283Value, chunk0021SuffixChars00 ++ tail)).bind
        (chunk0021AfterValue00 (fuel + 57) acc) :=
      congrArg (fun result => result.bind (chunk0021AfterValue00 (fuel + 57) acc))
        (value_fragment0099283 (fuel + 29) (chunk0021SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 57) (SourceJson.white tail) (chunk0021Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0021_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0022_before_reader"
  err.flush

noncomputable def chunk0022LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0022SuffixChars00 : List Char := [',']
noncomputable def chunk0022Chars00 : List Char := chunk0022LeadChars00 ++ fragment0101144Chars ++ chunk0022SuffixChars00
noncomputable def chunk0022Push00 (acc : List SourceJson) : List SourceJson := fragment0101144Value :: acc

noncomputable def chunk0022AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0022_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 57)
      (SourceJson.white (chunk0022LeadChars00 ++ (fragment0101144Chars ++ rest))) acc =
      (SourceJson.value (fuel + 56) (fragment0101144Chars ++ rest)).bind
        (chunk0022AfterValue00 (fuel + 56) acc) := by rfl

theorem array_chunk0022 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 57) (SourceJson.white (chunk0022Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 56) (SourceJson.white tail) (chunk0022Push00 acc) := by
  have hinput : chunk0022Chars00 ++ tail = chunk0022LeadChars00 ++ (fragment0101144Chars ++ (chunk0022SuffixChars00 ++ tail)) := by
    simp only [chunk0022Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 57) (SourceJson.white (chunk0022Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 57)
          (SourceJson.white (chunk0022LeadChars00 ++ (fragment0101144Chars ++ (chunk0022SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 57) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 56) (fragment0101144Chars ++ (chunk0022SuffixChars00 ++ tail))).bind
        (chunk0022AfterValue00 (fuel + 56) acc) := array_chunk0022_head fuel (chunk0022SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0101144Value, chunk0022SuffixChars00 ++ tail)).bind
        (chunk0022AfterValue00 (fuel + 56) acc) :=
      congrArg (fun result => result.bind (chunk0022AfterValue00 (fuel + 56) acc))
        (value_fragment0101144 (fuel + 35) (chunk0022SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 56) (SourceJson.white tail) (chunk0022Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0022_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0023_before_reader"
  err.flush

noncomputable def chunk0023Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '6', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0023Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['3'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['1', '2'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['3'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['8']), .number (String.ofList ['1', '0'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['3']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '1'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['7']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '2'])], .arr [.number (String.ofList ['7']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2'])], .arr [.number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['6']))]) :: (acc)

theorem array_chunk0023 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 56) (SourceJson.white (chunk0023Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 55) (SourceJson.white tail) (chunk0023Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0023_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0016Chars00 ++ chunk0017Chars00 ++ chunk0018Chars00 ++ chunk0019Chars00 ++ chunk0020Chars00 ++ chunk0021Chars00 ++ chunk0022Chars00 ++ chunk0023Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0023Push00 (chunk0022Push00 (chunk0021Push00 (chunk0020Push00 (chunk0019Push00 (chunk0018Push00 (chunk0017Push00 (chunk0016Push00 (acc))))))))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 63) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 55) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0016Chars00 ++ (chunk0017Chars00 ++ (chunk0018Chars00 ++ (chunk0019Chars00 ++ (chunk0020Chars00 ++ (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail)))))))) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 63) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 63) (SourceJson.white (chunk0016Chars00 ++ (chunk0017Chars00 ++ (chunk0018Chars00 ++ (chunk0019Chars00 ++ (chunk0020Chars00 ++ (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail)))))))))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 63) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 62) (SourceJson.white (chunk0017Chars00 ++ (chunk0018Chars00 ++ (chunk0019Chars00 ++ (chunk0020Chars00 ++ (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail))))))))) (chunk0016Push00 (acc)) := array_chunk0016 fuel (chunk0017Chars00 ++ (chunk0018Chars00 ++ (chunk0019Chars00 ++ (chunk0020Chars00 ++ (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail)))))))) (acc)
    _ = SourceJson.array (fuel + 61) (SourceJson.white (chunk0018Chars00 ++ (chunk0019Chars00 ++ (chunk0020Chars00 ++ (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail)))))))) (chunk0017Push00 (chunk0016Push00 (acc))) := array_chunk0017 fuel (chunk0018Chars00 ++ (chunk0019Chars00 ++ (chunk0020Chars00 ++ (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail))))))) (chunk0016Push00 (acc))
    _ = SourceJson.array (fuel + 60) (SourceJson.white (chunk0019Chars00 ++ (chunk0020Chars00 ++ (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail))))))) (chunk0018Push00 (chunk0017Push00 (chunk0016Push00 (acc)))) := array_chunk0018 fuel (chunk0019Chars00 ++ (chunk0020Chars00 ++ (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail)))))) (chunk0017Push00 (chunk0016Push00 (acc)))
    _ = SourceJson.array (fuel + 59) (SourceJson.white (chunk0020Chars00 ++ (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail)))))) (chunk0019Push00 (chunk0018Push00 (chunk0017Push00 (chunk0016Push00 (acc))))) := array_chunk0019 fuel (chunk0020Chars00 ++ (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail))))) (chunk0018Push00 (chunk0017Push00 (chunk0016Push00 (acc))))
    _ = SourceJson.array (fuel + 58) (SourceJson.white (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail))))) (chunk0020Push00 (chunk0019Push00 (chunk0018Push00 (chunk0017Push00 (chunk0016Push00 (acc)))))) := array_chunk0020 fuel (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail)))) (chunk0019Push00 (chunk0018Push00 (chunk0017Push00 (chunk0016Push00 (acc)))))
    _ = SourceJson.array (fuel + 57) (SourceJson.white (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail)))) (chunk0021Push00 (chunk0020Push00 (chunk0019Push00 (chunk0018Push00 (chunk0017Push00 (chunk0016Push00 (acc))))))) := array_chunk0021 fuel (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail))) (chunk0020Push00 (chunk0019Push00 (chunk0018Push00 (chunk0017Push00 (chunk0016Push00 (acc))))))
    _ = SourceJson.array (fuel + 56) (SourceJson.white (chunk0023Chars00 ++ (tail))) (chunk0022Push00 (chunk0021Push00 (chunk0020Push00 (chunk0019Push00 (chunk0018Push00 (chunk0017Push00 (chunk0016Push00 (acc)))))))) := array_chunk0022 fuel (chunk0023Chars00 ++ (tail)) (chunk0021Push00 (chunk0020Push00 (chunk0019Push00 (chunk0018Push00 (chunk0017Push00 (chunk0016Push00 (acc)))))))
    _ = SourceJson.array (fuel + 55) (SourceJson.white tail) (blockPush acc) := array_chunk0023 fuel (tail) (chunk0022Push00 (chunk0021Push00 (chunk0020Push00 (chunk0019Push00 (chunk0018Push00 (chunk0017Push00 (chunk0016Push00 (acc))))))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 94527).take 8399 = blockChars := by rfl

theorem block_original_split : sourceRest 94527 = blockChars ++ sourceRest 102926 := by
  calc
    sourceRest 94527 = (sourceRest 94527).take 8399 ++ (sourceRest 94527).drop 8399 :=
      (List.take_append_drop 8399 (sourceRest 94527)).symm
    _ = blockChars ++ (sourceRest 94527).drop 8399 :=
      congrArg (fun part => part ++ (sourceRest 94527).drop 8399) block_original_prefix
    _ = blockChars ++ sourceRest 102926 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 94527 8399)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 63) (SourceJson.white (sourceRest 94527)) acc =
      SourceJson.array (fuel + 55) (SourceJson.white (sourceRest 102926)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 63) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 102926) acc)

#print axioms array_fragment0094818_chunk_000
#print axioms array_fragment0094818_chunk_001
#print axioms array_fragment0094818_chunk_002
#print axioms array_fragment0094818_chunk_003
#print axioms value_fragment0094818
#print axioms object_fragment0094533_field_000
#print axioms object_fragment0094533_field_001
#print axioms object_fragment0094533_field_002
#print axioms object_fragment0094533_field_003_header
#print axioms object_fragment0094533_field_003
#print axioms object_fragment0094533_field_004
#print axioms value_fragment0094533
#print axioms object_fragment0096355_field_000
#print axioms object_fragment0096355_field_001
#print axioms object_fragment0096355_field_002
#print axioms object_fragment0096355_field_003
#print axioms object_fragment0096355_field_004
#print axioms value_fragment0096355
#print axioms array_fragment0097435_chunk_000
#print axioms array_fragment0097435_chunk_001
#print axioms array_fragment0097435_chunk_002
#print axioms array_fragment0097435_chunk_003
#print axioms value_fragment0097435
#print axioms object_fragment0097188_field_000
#print axioms object_fragment0097188_field_001
#print axioms object_fragment0097188_field_002
#print axioms object_fragment0097188_field_003_header
#print axioms object_fragment0097188_field_003
#print axioms object_fragment0097188_field_004
#print axioms value_fragment0097188
#print axioms array_fragment0099606_chunk_000
#print axioms array_fragment0099606_chunk_001
#print axioms array_fragment0099606_chunk_002
#print axioms array_fragment0099606_chunk_003
#print axioms value_fragment0099606
#print axioms object_fragment0099283_field_000
#print axioms object_fragment0099283_field_001
#print axioms object_fragment0099283_field_002
#print axioms object_fragment0099283_field_003_header
#print axioms object_fragment0099283_field_003
#print axioms object_fragment0099283_field_004
#print axioms value_fragment0099283
#print axioms array_fragment0101377_chunk_000
#print axioms array_fragment0101377_chunk_001
#print axioms array_fragment0101377_chunk_002
#print axioms array_fragment0101377_chunk_003
#print axioms value_fragment0101377
#print axioms object_fragment0101144_field_000
#print axioms object_fragment0101144_field_001
#print axioms object_fragment0101144_field_002
#print axioms object_fragment0101144_field_003_header
#print axioms object_fragment0101144_field_003
#print axioms object_fragment0101144_field_004
#print axioms value_fragment0101144
#print axioms array_chunk0016_head
#print axioms array_chunk0016
#print axioms array_chunk0017_head
#print axioms array_chunk0017
#print axioms array_chunk0018_head
#print axioms array_chunk0018
#print axioms array_chunk0019
#print axioms array_chunk0020
#print axioms array_chunk0021_head
#print axioms array_chunk0021
#print axioms array_chunk0022_head
#print axioms array_chunk0022
#print axioms array_chunk0023
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end FaceLedgerBlock002

end ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing
