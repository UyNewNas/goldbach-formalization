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

namespace FaceLedgerBlock014

noncomputable def fragment0205719Acc00000 : List SourceJson := []

noncomputable def fragment0205719Chunk000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0205719Chunk000Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['3', '6'])]) :: ((.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '6']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4'])]) :: (acc))

theorem array_fragment0205719_chunk_000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 19) (SourceJson.white (fragment0205719Chunk000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 17) (SourceJson.white tail) (fragment0205719Chunk000Push00 acc) := by
  rfl

noncomputable def fragment0205719Acc00100 : List SourceJson := fragment0205719Chunk000Push00 fragment0205719Acc00000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0205719_array_chunk_000"
  err.flush

noncomputable def fragment0205719Chunk001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0205719Chunk001Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['8']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '6']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '4']), .number (String.ofList ['3', '0']), .number (String.ofList ['3', '6'])]) :: ((.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '6']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['3', '0']), .number (String.ofList ['3', '6'])]) :: (acc))

theorem array_fragment0205719_chunk_001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 17) (SourceJson.white (fragment0205719Chunk001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 15) (SourceJson.white tail) (fragment0205719Chunk001Push00 acc) := by
  rfl

noncomputable def fragment0205719Acc00200 : List SourceJson := fragment0205719Chunk001Push00 fragment0205719Acc00100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0205719_array_chunk_001"
  err.flush

noncomputable def fragment0205719Chunk002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0205719Chunk002Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '6']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['3', '0']), .number (String.ofList ['3', '6'])]) :: ((.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '6']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['3', '0']), .number (String.ofList ['3', '6'])]) :: (acc))

theorem array_fragment0205719_chunk_002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 15) (SourceJson.white (fragment0205719Chunk002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 13) (SourceJson.white tail) (fragment0205719Chunk002Push00 acc) := by
  rfl

noncomputable def fragment0205719Acc00300 : List SourceJson := fragment0205719Chunk002Push00 fragment0205719Acc00200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0205719_array_chunk_002"
  err.flush

noncomputable def fragment0205719Chunk003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']']
noncomputable def fragment0205719Chunk003Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1', '6']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['3', '0'])]) :: ((.arr [.number (String.ofList ['3']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['3', '0']), .number (String.ofList ['3', '6'])]) :: (acc))

theorem array_fragment0205719_chunk_003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 13) (SourceJson.white (fragment0205719Chunk003Chars00 ++ tail)) acc =
      .ok (.arr ((fragment0205719Chunk003Push00 acc).reverse), tail) := by
  rfl

noncomputable def fragment0205719Acc00400 : List SourceJson := fragment0205719Chunk003Push00 fragment0205719Acc00300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0205719_array_chunk_003"
  err.flush

noncomputable def fragment0205719Chars : List Char := '[' :: (fragment0205719Chunk000Chars00 ++ fragment0205719Chunk001Chars00 ++ fragment0205719Chunk002Chars00 ++ fragment0205719Chunk003Chars00)
noncomputable def fragment0205719Value : SourceJson := .arr (fragment0205719Acc00400.reverse)

theorem value_fragment0205719 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 20) (fragment0205719Chars ++ tail) =
      .ok (fragment0205719Value, tail) := by
  have hinput : fragment0205719Chars ++ tail = '[' :: (fragment0205719Chunk000Chars00 ++ (fragment0205719Chunk001Chars00 ++ (fragment0205719Chunk002Chars00 ++ (fragment0205719Chunk003Chars00 ++ (tail))))) := by
    simp only [fragment0205719Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 20) (fragment0205719Chars ++ tail) =
        SourceJson.value (fuel + 20) ('[' :: (fragment0205719Chunk000Chars00 ++ (fragment0205719Chunk001Chars00 ++ (fragment0205719Chunk002Chars00 ++ (fragment0205719Chunk003Chars00 ++ (tail)))))) :=
      congrArg (SourceJson.value (fuel + 20)) hinput
    _ = SourceJson.array (fuel + 19) (SourceJson.white (fragment0205719Chunk000Chars00 ++ (fragment0205719Chunk001Chars00 ++ (fragment0205719Chunk002Chars00 ++ (fragment0205719Chunk003Chars00 ++ (tail)))))) fragment0205719Acc00000 := by rfl
    _ = SourceJson.array (fuel + 17) (SourceJson.white (fragment0205719Chunk001Chars00 ++ (fragment0205719Chunk002Chars00 ++ (fragment0205719Chunk003Chars00 ++ (tail))))) fragment0205719Acc00100 := array_fragment0205719_chunk_000 fuel (fragment0205719Chunk001Chars00 ++ (fragment0205719Chunk002Chars00 ++ (fragment0205719Chunk003Chars00 ++ (tail)))) fragment0205719Acc00000
    _ = SourceJson.array (fuel + 15) (SourceJson.white (fragment0205719Chunk002Chars00 ++ (fragment0205719Chunk003Chars00 ++ (tail)))) fragment0205719Acc00200 := array_fragment0205719_chunk_001 fuel (fragment0205719Chunk002Chars00 ++ (fragment0205719Chunk003Chars00 ++ (tail))) fragment0205719Acc00100
    _ = SourceJson.array (fuel + 13) (SourceJson.white (fragment0205719Chunk003Chars00 ++ (tail))) fragment0205719Acc00300 := array_fragment0205719_chunk_002 fuel (fragment0205719Chunk003Chars00 ++ (tail)) fragment0205719Acc00200
    _ = .ok (fragment0205719Value, tail) := array_fragment0205719_chunk_003 fuel (tail) fragment0205719Acc00300

noncomputable def fragment0205470Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0205470Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0205470Field000Value00 : SourceJson := .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '6']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['3', '0']), .number (String.ofList ['3', '6'])]
noncomputable def fragment0205470Acc00100 : List (String × SourceJson) := (fragment0205470Field000Key00, fragment0205470Field000Value00) :: fragment0205470Acc00000
noncomputable def fragment0205470Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0205470_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 24) (SourceJson.white (fragment0205470Field000Chars00 ++ tail)) fragment0205470Acc00000 =
      SourceJson.object (fuel + 23) (SourceJson.white tail) fragment0205470Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0205470_object_field_000"
  err.flush

noncomputable def fragment0205470Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0205470Field001Value00 : SourceJson := .number (String.ofList ['6'])
noncomputable def fragment0205470Acc00200 : List (String × SourceJson) := (fragment0205470Field001Key00, fragment0205470Field001Value00) :: fragment0205470Acc00100
noncomputable def fragment0205470Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '6', ',']

theorem object_fragment0205470_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 23) (SourceJson.white (fragment0205470Field001Chars00 ++ tail)) fragment0205470Acc00100 =
      SourceJson.object (fuel + 22) (SourceJson.white tail) fragment0205470Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0205470_object_field_001"
  err.flush

noncomputable def fragment0205470Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0205470Field002Value00 : SourceJson := .number (String.ofList ['3', '6'])
noncomputable def fragment0205470Acc00300 : List (String × SourceJson) := (fragment0205470Field002Key00, fragment0205470Field002Value00) :: fragment0205470Acc00200
noncomputable def fragment0205470Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '3', '6', ',']

theorem object_fragment0205470_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 22) (SourceJson.white (fragment0205470Field002Chars00 ++ tail)) fragment0205470Acc00200 =
      SourceJson.object (fuel + 21) (SourceJson.white tail) fragment0205470Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0205470_object_field_002"
  err.flush

noncomputable def fragment0205470Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0205470Field003Value00 : SourceJson := fragment0205719Value
noncomputable def fragment0205470Acc00400 : List (String × SourceJson) := (fragment0205470Field003Key00, fragment0205470Field003Value00) :: fragment0205470Acc00300
noncomputable def fragment0205470Field003HeaderChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ']
noncomputable def fragment0205470Field003SuffixChars00 : List Char := [',']
noncomputable def fragment0205470Field003Chars00 : List Char := fragment0205470Field003HeaderChars00 ++ fragment0205719Chars ++ fragment0205470Field003SuffixChars00

noncomputable def fragment0205470Field003AfterValue00 (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending => .ok (.obj (((fragment0205470Field003Key00, result.1) :: fragment0205470Acc00300).reverse), ending)
  | ',' :: ending => SourceJson.object fuel (SourceJson.white ending) ((fragment0205470Field003Key00, result.1) :: fragment0205470Acc00300)
  | _ => .error "object separator missing"

theorem object_fragment0205470_field_003_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 21) (SourceJson.white (fragment0205470Field003HeaderChars00 ++ rest)) fragment0205470Acc00300 =
      (SourceJson.value (fuel + 20) rest).bind (fragment0205470Field003AfterValue00 (fuel + 20)) := by rfl

theorem object_fragment0205470_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 21) (SourceJson.white (fragment0205470Field003Chars00 ++ tail)) fragment0205470Acc00300 =
      SourceJson.object (fuel + 20) (SourceJson.white tail) fragment0205470Acc00400 := by
  have hinput : fragment0205470Field003Chars00 ++ tail = fragment0205470Field003HeaderChars00 ++ (fragment0205719Chars ++ (fragment0205470Field003SuffixChars00 ++ tail)) := by
    simp only [fragment0205470Field003Chars00, List.append_assoc]
  calc
    SourceJson.object (fuel + 21) (SourceJson.white (fragment0205470Field003Chars00 ++ tail)) fragment0205470Acc00300 =
        SourceJson.object (fuel + 21)
          (SourceJson.white (fragment0205470Field003HeaderChars00 ++ (fragment0205719Chars ++ (fragment0205470Field003SuffixChars00 ++ tail)))) fragment0205470Acc00300 :=
      congrArg (fun s => SourceJson.object (fuel + 21) (SourceJson.white s) fragment0205470Acc00300) hinput
    _ = (SourceJson.value (fuel + 20) (fragment0205719Chars ++ (fragment0205470Field003SuffixChars00 ++ tail))).bind
        (fragment0205470Field003AfterValue00 (fuel + 20)) := object_fragment0205470_field_003_header fuel (fragment0205719Chars ++ (fragment0205470Field003SuffixChars00 ++ tail))
    _ = (Except.ok (fragment0205719Value, fragment0205470Field003SuffixChars00 ++ tail)).bind (fragment0205470Field003AfterValue00 (fuel + 20)) :=
      congrArg (fun result => result.bind (fragment0205470Field003AfterValue00 (fuel + 20)))
        (value_fragment0205719 (fuel + 0) (fragment0205470Field003SuffixChars00 ++ tail))
    _ = SourceJson.object (fuel + 20) (SourceJson.white tail) fragment0205470Acc00400 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0205470_object_field_003"
  err.flush

noncomputable def fragment0205470Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0205470Field004Value00 : SourceJson := .number (String.ofList ['6'])
noncomputable def fragment0205470Acc00500 : List (String × SourceJson) := (fragment0205470Field004Key00, fragment0205470Field004Value00) :: fragment0205470Acc00400
noncomputable def fragment0205470Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '6', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0205470_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 20) (SourceJson.white (fragment0205470Field004Chars00 ++ tail)) fragment0205470Acc00400 =
      .ok (.obj (fragment0205470Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0205470_object_field_004"
  err.flush

noncomputable def fragment0205470Chars : List Char := '{' :: (fragment0205470Field000Chars00 ++ fragment0205470Field001Chars00 ++ fragment0205470Field002Chars00 ++ fragment0205470Field003Chars00 ++ fragment0205470Field004Chars00)
noncomputable def fragment0205470Value : SourceJson := .obj (fragment0205470Acc00500.reverse)

theorem value_fragment0205470 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 25) (fragment0205470Chars ++ tail) =
      .ok (fragment0205470Value, tail) := by
  have hinput : fragment0205470Chars ++ tail = '{' :: (fragment0205470Field000Chars00 ++ (fragment0205470Field001Chars00 ++ (fragment0205470Field002Chars00 ++ (fragment0205470Field003Chars00 ++ (fragment0205470Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0205470Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 25) (fragment0205470Chars ++ tail) =
        SourceJson.value (fuel + 25) ('{' :: (fragment0205470Field000Chars00 ++ (fragment0205470Field001Chars00 ++ (fragment0205470Field002Chars00 ++ (fragment0205470Field003Chars00 ++ (fragment0205470Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 25)) hinput
    _ = SourceJson.object (fuel + 24) (SourceJson.white (fragment0205470Field000Chars00 ++ (fragment0205470Field001Chars00 ++ (fragment0205470Field002Chars00 ++ (fragment0205470Field003Chars00 ++ (fragment0205470Field004Chars00 ++ (tail))))))) fragment0205470Acc00000 := by rfl
    _ = SourceJson.object (fuel + 23) (SourceJson.white (fragment0205470Field001Chars00 ++ (fragment0205470Field002Chars00 ++ (fragment0205470Field003Chars00 ++ (fragment0205470Field004Chars00 ++ (tail)))))) fragment0205470Acc00100 := object_fragment0205470_field_000 fuel (fragment0205470Field001Chars00 ++ (fragment0205470Field002Chars00 ++ (fragment0205470Field003Chars00 ++ (fragment0205470Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 22) (SourceJson.white (fragment0205470Field002Chars00 ++ (fragment0205470Field003Chars00 ++ (fragment0205470Field004Chars00 ++ (tail))))) fragment0205470Acc00200 := object_fragment0205470_field_001 fuel (fragment0205470Field002Chars00 ++ (fragment0205470Field003Chars00 ++ (fragment0205470Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 21) (SourceJson.white (fragment0205470Field003Chars00 ++ (fragment0205470Field004Chars00 ++ (tail)))) fragment0205470Acc00300 := object_fragment0205470_field_002 fuel (fragment0205470Field003Chars00 ++ (fragment0205470Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 20) (SourceJson.white (fragment0205470Field004Chars00 ++ (tail))) fragment0205470Acc00400 := object_fragment0205470_field_003 fuel (fragment0205470Field004Chars00 ++ (tail))
    _ = .ok (fragment0205470Value, tail) := object_fragment0205470_field_004 fuel (tail)

noncomputable def fragment0207003Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0207003Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0207003Field000Value00 : SourceJson := .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '6']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3'])]
noncomputable def fragment0207003Acc00100 : List (String × SourceJson) := (fragment0207003Field000Key00, fragment0207003Field000Value00) :: fragment0207003Acc00000
noncomputable def fragment0207003Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0207003_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 18) (SourceJson.white (fragment0207003Field000Chars00 ++ tail)) fragment0207003Acc00000 =
      SourceJson.object (fuel + 17) (SourceJson.white tail) fragment0207003Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0207003_object_field_000"
  err.flush

noncomputable def fragment0207003Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0207003Field001Value00 : SourceJson := .number (String.ofList ['4'])
noncomputable def fragment0207003Acc00200 : List (String × SourceJson) := (fragment0207003Field001Key00, fragment0207003Field001Value00) :: fragment0207003Acc00100
noncomputable def fragment0207003Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '4', ',']

theorem object_fragment0207003_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 17) (SourceJson.white (fragment0207003Field001Chars00 ++ tail)) fragment0207003Acc00100 =
      SourceJson.object (fuel + 16) (SourceJson.white tail) fragment0207003Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0207003_object_field_001"
  err.flush

noncomputable def fragment0207003Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0207003Field002Value00 : SourceJson := .number (String.ofList ['2', '3'])
noncomputable def fragment0207003Acc00300 : List (String × SourceJson) := (fragment0207003Field002Key00, fragment0207003Field002Value00) :: fragment0207003Acc00200
noncomputable def fragment0207003Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '2', '3', ',']

theorem object_fragment0207003_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 16) (SourceJson.white (fragment0207003Field002Chars00 ++ tail)) fragment0207003Acc00200 =
      SourceJson.object (fuel + 15) (SourceJson.white tail) fragment0207003Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0207003_object_field_002"
  err.flush

noncomputable def fragment0207003Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0207003Field003Value00 : SourceJson := .arr [.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['8']), .number (String.ofList ['1', '0'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['8']), .number (String.ofList ['1', '6']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '6']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '3'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '6']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3'])], .arr [.number (String.ofList ['3']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3'])], .arr [.number (String.ofList ['1', '6']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3'])]]
noncomputable def fragment0207003Acc00400 : List (String × SourceJson) := (fragment0207003Field003Key00, fragment0207003Field003Value00) :: fragment0207003Acc00300
noncomputable def fragment0207003Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0207003_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 15) (SourceJson.white (fragment0207003Field003Chars00 ++ tail)) fragment0207003Acc00300 =
      SourceJson.object (fuel + 14) (SourceJson.white tail) fragment0207003Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0207003_object_field_003"
  err.flush

noncomputable def fragment0207003Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0207003Field004Value00 : SourceJson := .number (String.ofList ['4'])
noncomputable def fragment0207003Acc00500 : List (String × SourceJson) := (fragment0207003Field004Key00, fragment0207003Field004Value00) :: fragment0207003Acc00400
noncomputable def fragment0207003Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0207003_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 14) (SourceJson.white (fragment0207003Field004Chars00 ++ tail)) fragment0207003Acc00400 =
      .ok (.obj (fragment0207003Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0207003_object_field_004"
  err.flush

noncomputable def fragment0207003Chars : List Char := '{' :: (fragment0207003Field000Chars00 ++ fragment0207003Field001Chars00 ++ fragment0207003Field002Chars00 ++ fragment0207003Field003Chars00 ++ fragment0207003Field004Chars00)
noncomputable def fragment0207003Value : SourceJson := .obj (fragment0207003Acc00500.reverse)

theorem value_fragment0207003 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 19) (fragment0207003Chars ++ tail) =
      .ok (fragment0207003Value, tail) := by
  have hinput : fragment0207003Chars ++ tail = '{' :: (fragment0207003Field000Chars00 ++ (fragment0207003Field001Chars00 ++ (fragment0207003Field002Chars00 ++ (fragment0207003Field003Chars00 ++ (fragment0207003Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0207003Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 19) (fragment0207003Chars ++ tail) =
        SourceJson.value (fuel + 19) ('{' :: (fragment0207003Field000Chars00 ++ (fragment0207003Field001Chars00 ++ (fragment0207003Field002Chars00 ++ (fragment0207003Field003Chars00 ++ (fragment0207003Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 19)) hinput
    _ = SourceJson.object (fuel + 18) (SourceJson.white (fragment0207003Field000Chars00 ++ (fragment0207003Field001Chars00 ++ (fragment0207003Field002Chars00 ++ (fragment0207003Field003Chars00 ++ (fragment0207003Field004Chars00 ++ (tail))))))) fragment0207003Acc00000 := by rfl
    _ = SourceJson.object (fuel + 17) (SourceJson.white (fragment0207003Field001Chars00 ++ (fragment0207003Field002Chars00 ++ (fragment0207003Field003Chars00 ++ (fragment0207003Field004Chars00 ++ (tail)))))) fragment0207003Acc00100 := object_fragment0207003_field_000 fuel (fragment0207003Field001Chars00 ++ (fragment0207003Field002Chars00 ++ (fragment0207003Field003Chars00 ++ (fragment0207003Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 16) (SourceJson.white (fragment0207003Field002Chars00 ++ (fragment0207003Field003Chars00 ++ (fragment0207003Field004Chars00 ++ (tail))))) fragment0207003Acc00200 := object_fragment0207003_field_001 fuel (fragment0207003Field002Chars00 ++ (fragment0207003Field003Chars00 ++ (fragment0207003Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 15) (SourceJson.white (fragment0207003Field003Chars00 ++ (fragment0207003Field004Chars00 ++ (tail)))) fragment0207003Acc00300 := object_fragment0207003_field_002 fuel (fragment0207003Field003Chars00 ++ (fragment0207003Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 14) (SourceJson.white (fragment0207003Field004Chars00 ++ (tail))) fragment0207003Acc00400 := object_fragment0207003_field_003 fuel (fragment0207003Field004Chars00 ++ (tail))
    _ = .ok (fragment0207003Value, tail) := object_fragment0207003_field_004 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0040_before_reader"
  err.flush

noncomputable def chunk0040LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0040SuffixChars00 : List Char := [',']
noncomputable def chunk0040Chars00 : List Char := chunk0040LeadChars00 ++ fragment0205470Chars ++ chunk0040SuffixChars00
noncomputable def chunk0040Push00 (acc : List SourceJson) : List SourceJson := fragment0205470Value :: acc

noncomputable def chunk0040AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0040_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 52)
      (SourceJson.white (chunk0040LeadChars00 ++ (fragment0205470Chars ++ rest))) acc =
      (SourceJson.value (fuel + 51) (fragment0205470Chars ++ rest)).bind
        (chunk0040AfterValue00 (fuel + 51) acc) := by rfl

theorem array_chunk0040 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 52) (SourceJson.white (chunk0040Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 51) (SourceJson.white tail) (chunk0040Push00 acc) := by
  have hinput : chunk0040Chars00 ++ tail = chunk0040LeadChars00 ++ (fragment0205470Chars ++ (chunk0040SuffixChars00 ++ tail)) := by
    simp only [chunk0040Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 52) (SourceJson.white (chunk0040Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 52)
          (SourceJson.white (chunk0040LeadChars00 ++ (fragment0205470Chars ++ (chunk0040SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 52) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 51) (fragment0205470Chars ++ (chunk0040SuffixChars00 ++ tail))).bind
        (chunk0040AfterValue00 (fuel + 51) acc) := array_chunk0040_head fuel (chunk0040SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0205470Value, chunk0040SuffixChars00 ++ tail)).bind
        (chunk0040AfterValue00 (fuel + 51) acc) :=
      congrArg (fun result => result.bind (chunk0040AfterValue00 (fuel + 51) acc))
        (value_fragment0205470 (fuel + 26) (chunk0040SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 51) (SourceJson.white tail) (chunk0040Push00 acc) := by rfl

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
noncomputable def chunk0041Chars00 : List Char := chunk0041LeadChars00 ++ fragment0207003Chars ++ chunk0041SuffixChars00
noncomputable def chunk0041Push00 (acc : List SourceJson) : List SourceJson := fragment0207003Value :: acc

noncomputable def chunk0041AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0041_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 51)
      (SourceJson.white (chunk0041LeadChars00 ++ (fragment0207003Chars ++ rest))) acc =
      (SourceJson.value (fuel + 50) (fragment0207003Chars ++ rest)).bind
        (chunk0041AfterValue00 (fuel + 50) acc) := by rfl

theorem array_chunk0041 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 51) (SourceJson.white (chunk0041Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 50) (SourceJson.white tail) (chunk0041Push00 acc) := by
  have hinput : chunk0041Chars00 ++ tail = chunk0041LeadChars00 ++ (fragment0207003Chars ++ (chunk0041SuffixChars00 ++ tail)) := by
    simp only [chunk0041Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 51) (SourceJson.white (chunk0041Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 51)
          (SourceJson.white (chunk0041LeadChars00 ++ (fragment0207003Chars ++ (chunk0041SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 51) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 50) (fragment0207003Chars ++ (chunk0041SuffixChars00 ++ tail))).bind
        (chunk0041AfterValue00 (fuel + 50) acc) := array_chunk0041_head fuel (chunk0041SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0207003Value, chunk0041SuffixChars00 ++ tail)).bind
        (chunk0041AfterValue00 (fuel + 50) acc) :=
      congrArg (fun result => result.bind (chunk0041AfterValue00 (fuel + 50) acc))
        (value_fragment0207003 (fuel + 31) (chunk0041SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 50) (SourceJson.white tail) (chunk0041Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0041_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0042_before_reader"
  err.flush

noncomputable def chunk0042Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '3', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0042Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['8']), .number (String.ofList ['1', '6']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['3'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['2', '1'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['8'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['1', '6']), .number (String.ofList ['2', '0'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['8']), .number (String.ofList ['1', '6']), .number (String.ofList ['2', '1'])], .arr [.number (String.ofList ['3']), .number (String.ofList ['8']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1'])], .arr [.number (String.ofList ['1', '6']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['3']))]) :: (acc)

theorem array_chunk0042 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 50) (SourceJson.white (chunk0042Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 49) (SourceJson.white tail) (chunk0042Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0042_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0043_before_reader"
  err.flush

noncomputable def chunk0043Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '2', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0043Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['1']), .number (String.ofList ['1', '6'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['1'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['1', '6'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['1'])], .arr [.number (String.ofList ['1', '6'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['1']))]) :: ((.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['1', '6']), .number (String.ofList ['2', '0'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['2'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['2', '0'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['1']), .number (String.ofList ['3'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['1', '6'])], .arr [.number (String.ofList ['3']), .number (String.ofList ['2', '0'])], .arr [.number (String.ofList ['1', '6']), .number (String.ofList ['2', '0'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['2']))]) :: (acc))

theorem array_chunk0043 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 49) (SourceJson.white (chunk0043Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 47) (SourceJson.white tail) (chunk0043Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0043_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0040Chars00 ++ chunk0041Chars00 ++ chunk0042Chars00 ++ chunk0043Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0043Push00 (chunk0042Push00 (chunk0041Push00 (chunk0040Push00 (acc))))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 52) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 47) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0040Chars00 ++ (chunk0041Chars00 ++ (chunk0042Chars00 ++ (chunk0043Chars00 ++ (tail)))) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 52) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 52) (SourceJson.white (chunk0040Chars00 ++ (chunk0041Chars00 ++ (chunk0042Chars00 ++ (chunk0043Chars00 ++ (tail)))))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 52) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 51) (SourceJson.white (chunk0041Chars00 ++ (chunk0042Chars00 ++ (chunk0043Chars00 ++ (tail))))) (chunk0040Push00 (acc)) := array_chunk0040 fuel (chunk0041Chars00 ++ (chunk0042Chars00 ++ (chunk0043Chars00 ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 50) (SourceJson.white (chunk0042Chars00 ++ (chunk0043Chars00 ++ (tail)))) (chunk0041Push00 (chunk0040Push00 (acc))) := array_chunk0041 fuel (chunk0042Chars00 ++ (chunk0043Chars00 ++ (tail))) (chunk0040Push00 (acc))
    _ = SourceJson.array (fuel + 49) (SourceJson.white (chunk0043Chars00 ++ (tail))) (chunk0042Push00 (chunk0041Push00 (chunk0040Push00 (acc)))) := array_chunk0042 fuel (chunk0043Chars00 ++ (tail)) (chunk0041Push00 (chunk0040Push00 (acc)))
    _ = SourceJson.array (fuel + 47) (SourceJson.white tail) (blockPush acc) := array_chunk0043 fuel (tail) (chunk0042Push00 (chunk0041Push00 (chunk0040Push00 (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 205464).take 3600 = blockChars := by rfl

theorem block_original_split : sourceRest 205464 = blockChars ++ sourceRest 209064 := by
  calc
    sourceRest 205464 = (sourceRest 205464).take 3600 ++ (sourceRest 205464).drop 3600 :=
      (List.take_append_drop 3600 (sourceRest 205464)).symm
    _ = blockChars ++ (sourceRest 205464).drop 3600 :=
      congrArg (fun part => part ++ (sourceRest 205464).drop 3600) block_original_prefix
    _ = blockChars ++ sourceRest 209064 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 205464 3600)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 52) (SourceJson.white (sourceRest 205464)) acc =
      SourceJson.array (fuel + 47) (SourceJson.white (sourceRest 209064)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 52) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 209064) acc)

#print axioms array_fragment0205719_chunk_000
#print axioms array_fragment0205719_chunk_001
#print axioms array_fragment0205719_chunk_002
#print axioms array_fragment0205719_chunk_003
#print axioms value_fragment0205719
#print axioms object_fragment0205470_field_000
#print axioms object_fragment0205470_field_001
#print axioms object_fragment0205470_field_002
#print axioms object_fragment0205470_field_003_header
#print axioms object_fragment0205470_field_003
#print axioms object_fragment0205470_field_004
#print axioms value_fragment0205470
#print axioms object_fragment0207003_field_000
#print axioms object_fragment0207003_field_001
#print axioms object_fragment0207003_field_002
#print axioms object_fragment0207003_field_003
#print axioms object_fragment0207003_field_004
#print axioms value_fragment0207003
#print axioms array_chunk0040_head
#print axioms array_chunk0040
#print axioms array_chunk0041_head
#print axioms array_chunk0041
#print axioms array_chunk0042
#print axioms array_chunk0043
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end FaceLedgerBlock014

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
