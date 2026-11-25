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

namespace FaceLedgerBlock015

noncomputable def fragment0210878Acc00000 : List SourceJson := []

noncomputable def fragment0210878Chunk000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0210878Chunk000Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '8']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4'])]) :: ((.arr [.number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3'])]) :: (acc))

theorem array_fragment0210878_chunk_000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 16) (SourceJson.white (fragment0210878Chunk000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 14) (SourceJson.white tail) (fragment0210878Chunk000Push00 acc) := by
  rfl

noncomputable def fragment0210878Acc00100 : List SourceJson := fragment0210878Chunk000Push00 fragment0210878Acc00000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0210878_array_chunk_000"
  err.flush

noncomputable def fragment0210878Chunk001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0210878Chunk001Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '2'])]) :: ((.arr [.number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4'])]) :: (acc))

theorem array_fragment0210878_chunk_001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 14) (SourceJson.white (fragment0210878Chunk001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 12) (SourceJson.white tail) (fragment0210878Chunk001Push00 acc) := by
  rfl

noncomputable def fragment0210878Acc00200 : List SourceJson := fragment0210878Chunk001Push00 fragment0210878Acc00100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0210878_array_chunk_001"
  err.flush

noncomputable def fragment0210878Chunk002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0210878Chunk002Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '4'])]) :: ((.arr [.number (String.ofList ['1', '4']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4'])]) :: (acc))

theorem array_fragment0210878_chunk_002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 12) (SourceJson.white (fragment0210878Chunk002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 10) (SourceJson.white tail) (fragment0210878Chunk002Push00 acc) := by
  rfl

noncomputable def fragment0210878Acc00300 : List SourceJson := fragment0210878Chunk002Push00 fragment0210878Acc00200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0210878_array_chunk_002"
  err.flush

noncomputable def fragment0210878Chunk003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']']
noncomputable def fragment0210878Chunk003Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1', '6']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4'])]) :: (acc)

theorem array_fragment0210878_chunk_003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 10) (SourceJson.white (fragment0210878Chunk003Chars00 ++ tail)) acc =
      .ok (.arr ((fragment0210878Chunk003Push00 acc).reverse), tail) := by
  rfl

noncomputable def fragment0210878Acc00400 : List SourceJson := fragment0210878Chunk003Push00 fragment0210878Acc00300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0210878_array_chunk_003"
  err.flush

noncomputable def fragment0210878Chars : List Char := '[' :: (fragment0210878Chunk000Chars00 ++ fragment0210878Chunk001Chars00 ++ fragment0210878Chunk002Chars00 ++ fragment0210878Chunk003Chars00)
noncomputable def fragment0210878Value : SourceJson := .arr (fragment0210878Acc00400.reverse)

theorem value_fragment0210878 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 17) (fragment0210878Chars ++ tail) =
      .ok (fragment0210878Value, tail) := by
  have hinput : fragment0210878Chars ++ tail = '[' :: (fragment0210878Chunk000Chars00 ++ (fragment0210878Chunk001Chars00 ++ (fragment0210878Chunk002Chars00 ++ (fragment0210878Chunk003Chars00 ++ (tail))))) := by
    simp only [fragment0210878Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 17) (fragment0210878Chars ++ tail) =
        SourceJson.value (fuel + 17) ('[' :: (fragment0210878Chunk000Chars00 ++ (fragment0210878Chunk001Chars00 ++ (fragment0210878Chunk002Chars00 ++ (fragment0210878Chunk003Chars00 ++ (tail)))))) :=
      congrArg (SourceJson.value (fuel + 17)) hinput
    _ = SourceJson.array (fuel + 16) (SourceJson.white (fragment0210878Chunk000Chars00 ++ (fragment0210878Chunk001Chars00 ++ (fragment0210878Chunk002Chars00 ++ (fragment0210878Chunk003Chars00 ++ (tail)))))) fragment0210878Acc00000 := by rfl
    _ = SourceJson.array (fuel + 14) (SourceJson.white (fragment0210878Chunk001Chars00 ++ (fragment0210878Chunk002Chars00 ++ (fragment0210878Chunk003Chars00 ++ (tail))))) fragment0210878Acc00100 := array_fragment0210878_chunk_000 fuel (fragment0210878Chunk001Chars00 ++ (fragment0210878Chunk002Chars00 ++ (fragment0210878Chunk003Chars00 ++ (tail)))) fragment0210878Acc00000
    _ = SourceJson.array (fuel + 12) (SourceJson.white (fragment0210878Chunk002Chars00 ++ (fragment0210878Chunk003Chars00 ++ (tail)))) fragment0210878Acc00200 := array_fragment0210878_chunk_001 fuel (fragment0210878Chunk002Chars00 ++ (fragment0210878Chunk003Chars00 ++ (tail))) fragment0210878Acc00100
    _ = SourceJson.array (fuel + 10) (SourceJson.white (fragment0210878Chunk003Chars00 ++ (tail))) fragment0210878Acc00300 := array_fragment0210878_chunk_002 fuel (fragment0210878Chunk003Chars00 ++ (tail)) fragment0210878Acc00200
    _ = .ok (fragment0210878Value, tail) := array_fragment0210878_chunk_003 fuel (tail) fragment0210878Acc00300

noncomputable def fragment0210652Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0210652Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0210652Field000Value00 : SourceJson := .arr [.number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4'])]
noncomputable def fragment0210652Acc00100 : List (String × SourceJson) := (fragment0210652Field000Key00, fragment0210652Field000Value00) :: fragment0210652Acc00000
noncomputable def fragment0210652Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0210652_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 21) (SourceJson.white (fragment0210652Field000Chars00 ++ tail)) fragment0210652Acc00000 =
      SourceJson.object (fuel + 20) (SourceJson.white tail) fragment0210652Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0210652_object_field_000"
  err.flush

noncomputable def fragment0210652Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0210652Field001Value00 : SourceJson := .number (String.ofList ['5'])
noncomputable def fragment0210652Acc00200 : List (String × SourceJson) := (fragment0210652Field001Key00, fragment0210652Field001Value00) :: fragment0210652Acc00100
noncomputable def fragment0210652Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '5', ',']

theorem object_fragment0210652_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 20) (SourceJson.white (fragment0210652Field001Chars00 ++ tail)) fragment0210652Acc00100 =
      SourceJson.object (fuel + 19) (SourceJson.white tail) fragment0210652Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0210652_object_field_001"
  err.flush

noncomputable def fragment0210652Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0210652Field002Value00 : SourceJson := .number (String.ofList ['2', '4'])
noncomputable def fragment0210652Acc00300 : List (String × SourceJson) := (fragment0210652Field002Key00, fragment0210652Field002Value00) :: fragment0210652Acc00200
noncomputable def fragment0210652Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '2', '4', ',']

theorem object_fragment0210652_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 19) (SourceJson.white (fragment0210652Field002Chars00 ++ tail)) fragment0210652Acc00200 =
      SourceJson.object (fuel + 18) (SourceJson.white tail) fragment0210652Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0210652_object_field_002"
  err.flush

noncomputable def fragment0210652Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0210652Field003Value00 : SourceJson := fragment0210878Value
noncomputable def fragment0210652Acc00400 : List (String × SourceJson) := (fragment0210652Field003Key00, fragment0210652Field003Value00) :: fragment0210652Acc00300
noncomputable def fragment0210652Field003HeaderChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ']
noncomputable def fragment0210652Field003SuffixChars00 : List Char := [',']
noncomputable def fragment0210652Field003Chars00 : List Char := fragment0210652Field003HeaderChars00 ++ fragment0210878Chars ++ fragment0210652Field003SuffixChars00

noncomputable def fragment0210652Field003AfterValue00 (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending => .ok (.obj (((fragment0210652Field003Key00, result.1) :: fragment0210652Acc00300).reverse), ending)
  | ',' :: ending => SourceJson.object fuel (SourceJson.white ending) ((fragment0210652Field003Key00, result.1) :: fragment0210652Acc00300)
  | _ => .error "object separator missing"

theorem object_fragment0210652_field_003_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 18) (SourceJson.white (fragment0210652Field003HeaderChars00 ++ rest)) fragment0210652Acc00300 =
      (SourceJson.value (fuel + 17) rest).bind (fragment0210652Field003AfterValue00 (fuel + 17)) := by rfl

theorem object_fragment0210652_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 18) (SourceJson.white (fragment0210652Field003Chars00 ++ tail)) fragment0210652Acc00300 =
      SourceJson.object (fuel + 17) (SourceJson.white tail) fragment0210652Acc00400 := by
  have hinput : fragment0210652Field003Chars00 ++ tail = fragment0210652Field003HeaderChars00 ++ (fragment0210878Chars ++ (fragment0210652Field003SuffixChars00 ++ tail)) := by
    simp only [fragment0210652Field003Chars00, List.append_assoc]
  calc
    SourceJson.object (fuel + 18) (SourceJson.white (fragment0210652Field003Chars00 ++ tail)) fragment0210652Acc00300 =
        SourceJson.object (fuel + 18)
          (SourceJson.white (fragment0210652Field003HeaderChars00 ++ (fragment0210878Chars ++ (fragment0210652Field003SuffixChars00 ++ tail)))) fragment0210652Acc00300 :=
      congrArg (fun s => SourceJson.object (fuel + 18) (SourceJson.white s) fragment0210652Acc00300) hinput
    _ = (SourceJson.value (fuel + 17) (fragment0210878Chars ++ (fragment0210652Field003SuffixChars00 ++ tail))).bind
        (fragment0210652Field003AfterValue00 (fuel + 17)) := object_fragment0210652_field_003_header fuel (fragment0210878Chars ++ (fragment0210652Field003SuffixChars00 ++ tail))
    _ = (Except.ok (fragment0210878Value, fragment0210652Field003SuffixChars00 ++ tail)).bind (fragment0210652Field003AfterValue00 (fuel + 17)) :=
      congrArg (fun result => result.bind (fragment0210652Field003AfterValue00 (fuel + 17)))
        (value_fragment0210878 (fuel + 0) (fragment0210652Field003SuffixChars00 ++ tail))
    _ = SourceJson.object (fuel + 17) (SourceJson.white tail) fragment0210652Acc00400 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0210652_object_field_003"
  err.flush

noncomputable def fragment0210652Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0210652Field004Value00 : SourceJson := .number (String.ofList ['5'])
noncomputable def fragment0210652Acc00500 : List (String × SourceJson) := (fragment0210652Field004Key00, fragment0210652Field004Value00) :: fragment0210652Acc00400
noncomputable def fragment0210652Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '5', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0210652_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 17) (SourceJson.white (fragment0210652Field004Chars00 ++ tail)) fragment0210652Acc00400 =
      .ok (.obj (fragment0210652Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0210652_object_field_004"
  err.flush

noncomputable def fragment0210652Chars : List Char := '{' :: (fragment0210652Field000Chars00 ++ fragment0210652Field001Chars00 ++ fragment0210652Field002Chars00 ++ fragment0210652Field003Chars00 ++ fragment0210652Field004Chars00)
noncomputable def fragment0210652Value : SourceJson := .obj (fragment0210652Acc00500.reverse)

theorem value_fragment0210652 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 22) (fragment0210652Chars ++ tail) =
      .ok (fragment0210652Value, tail) := by
  have hinput : fragment0210652Chars ++ tail = '{' :: (fragment0210652Field000Chars00 ++ (fragment0210652Field001Chars00 ++ (fragment0210652Field002Chars00 ++ (fragment0210652Field003Chars00 ++ (fragment0210652Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0210652Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 22) (fragment0210652Chars ++ tail) =
        SourceJson.value (fuel + 22) ('{' :: (fragment0210652Field000Chars00 ++ (fragment0210652Field001Chars00 ++ (fragment0210652Field002Chars00 ++ (fragment0210652Field003Chars00 ++ (fragment0210652Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 22)) hinput
    _ = SourceJson.object (fuel + 21) (SourceJson.white (fragment0210652Field000Chars00 ++ (fragment0210652Field001Chars00 ++ (fragment0210652Field002Chars00 ++ (fragment0210652Field003Chars00 ++ (fragment0210652Field004Chars00 ++ (tail))))))) fragment0210652Acc00000 := by rfl
    _ = SourceJson.object (fuel + 20) (SourceJson.white (fragment0210652Field001Chars00 ++ (fragment0210652Field002Chars00 ++ (fragment0210652Field003Chars00 ++ (fragment0210652Field004Chars00 ++ (tail)))))) fragment0210652Acc00100 := object_fragment0210652_field_000 fuel (fragment0210652Field001Chars00 ++ (fragment0210652Field002Chars00 ++ (fragment0210652Field003Chars00 ++ (fragment0210652Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 19) (SourceJson.white (fragment0210652Field002Chars00 ++ (fragment0210652Field003Chars00 ++ (fragment0210652Field004Chars00 ++ (tail))))) fragment0210652Acc00200 := object_fragment0210652_field_001 fuel (fragment0210652Field002Chars00 ++ (fragment0210652Field003Chars00 ++ (fragment0210652Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 18) (SourceJson.white (fragment0210652Field003Chars00 ++ (fragment0210652Field004Chars00 ++ (tail)))) fragment0210652Acc00300 := object_fragment0210652_field_002 fuel (fragment0210652Field003Chars00 ++ (fragment0210652Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 17) (SourceJson.white (fragment0210652Field004Chars00 ++ (tail))) fragment0210652Acc00400 := object_fragment0210652_field_003 fuel (fragment0210652Field004Chars00 ++ (tail))
    _ = .ok (fragment0210652Value, tail) := object_fragment0210652_field_004 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0044_before_reader"
  err.flush

noncomputable def chunk0044Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '2', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0044Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['2'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['5'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['2']), .number (String.ofList ['3'])], .arr [.number (String.ofList ['2']), .number (String.ofList ['4'])], .arr [.number (String.ofList ['3']), .number (String.ofList ['5'])], .arr [.number (String.ofList ['4']), .number (String.ofList ['5'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['2']))]) :: ((.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['2']), .number (String.ofList ['3'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['1'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['3'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['2'])], .arr [.number (String.ofList ['3'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['1']))]) :: (acc))

theorem array_chunk0044 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 47) (SourceJson.white (chunk0044Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 45) (SourceJson.white tail) (chunk0044Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0044_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0045_before_reader"
  err.flush

noncomputable def chunk0045Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0045Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['3']), .number (String.ofList ['5'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['1'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['5'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['3'])], .arr [.number (String.ofList ['5'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['1']))]) :: ((.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['2']), .number (String.ofList ['4'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['1'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['4'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['2'])], .arr [.number (String.ofList ['4'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['1']))]) :: (acc))

theorem array_chunk0045 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 45) (SourceJson.white (chunk0045Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 43) (SourceJson.white tail) (chunk0045Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0045_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0046_before_reader"
  err.flush

noncomputable def chunk0046Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0046Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['1', '4']), .number (String.ofList ['1', '5'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['1'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['1', '5'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['1', '4'])], .arr [.number (String.ofList ['1', '5'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['1']))]) :: ((.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['1', '4'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['1'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['1', '4'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['7'])], .arr [.number (String.ofList ['1', '4'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['1']))]) :: (acc))

theorem array_chunk0046 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 43) (SourceJson.white (chunk0046Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 41) (SourceJson.white tail) (chunk0046Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0046_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0047_before_reader"
  err.flush

noncomputable def chunk0047LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0047SuffixChars00 : List Char := [',']
noncomputable def chunk0047Chars00 : List Char := chunk0047LeadChars00 ++ fragment0210652Chars ++ chunk0047SuffixChars00
noncomputable def chunk0047Push00 (acc : List SourceJson) : List SourceJson := fragment0210652Value :: acc

noncomputable def chunk0047AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0047_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 41)
      (SourceJson.white (chunk0047LeadChars00 ++ (fragment0210652Chars ++ rest))) acc =
      (SourceJson.value (fuel + 40) (fragment0210652Chars ++ rest)).bind
        (chunk0047AfterValue00 (fuel + 40) acc) := by rfl

theorem array_chunk0047 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 41) (SourceJson.white (chunk0047Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 40) (SourceJson.white tail) (chunk0047Push00 acc) := by
  have hinput : chunk0047Chars00 ++ tail = chunk0047LeadChars00 ++ (fragment0210652Chars ++ (chunk0047SuffixChars00 ++ tail)) := by
    simp only [chunk0047Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 41) (SourceJson.white (chunk0047Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 41)
          (SourceJson.white (chunk0047LeadChars00 ++ (fragment0210652Chars ++ (chunk0047SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 41) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 40) (fragment0210652Chars ++ (chunk0047SuffixChars00 ++ tail))).bind
        (chunk0047AfterValue00 (fuel + 40) acc) := array_chunk0047_head fuel (chunk0047SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0210652Value, chunk0047SuffixChars00 ++ tail)).bind
        (chunk0047AfterValue00 (fuel + 40) acc) :=
      congrArg (fun result => result.bind (chunk0047AfterValue00 (fuel + 40) acc))
        (value_fragment0210652 (fuel + 18) (chunk0047SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 40) (SourceJson.white tail) (chunk0047Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0047_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0044Chars00 ++ chunk0045Chars00 ++ chunk0046Chars00 ++ chunk0047Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0047Push00 (chunk0046Push00 (chunk0045Push00 (chunk0044Push00 (acc))))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 47) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 40) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0044Chars00 ++ (chunk0045Chars00 ++ (chunk0046Chars00 ++ (chunk0047Chars00 ++ (tail)))) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 47) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 47) (SourceJson.white (chunk0044Chars00 ++ (chunk0045Chars00 ++ (chunk0046Chars00 ++ (chunk0047Chars00 ++ (tail)))))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 47) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 45) (SourceJson.white (chunk0045Chars00 ++ (chunk0046Chars00 ++ (chunk0047Chars00 ++ (tail))))) (chunk0044Push00 (acc)) := array_chunk0044 fuel (chunk0045Chars00 ++ (chunk0046Chars00 ++ (chunk0047Chars00 ++ (tail)))) (acc)
    _ = SourceJson.array (fuel + 43) (SourceJson.white (chunk0046Chars00 ++ (chunk0047Chars00 ++ (tail)))) (chunk0045Push00 (chunk0044Push00 (acc))) := array_chunk0045 fuel (chunk0046Chars00 ++ (chunk0047Chars00 ++ (tail))) (chunk0044Push00 (acc))
    _ = SourceJson.array (fuel + 41) (SourceJson.white (chunk0047Chars00 ++ (tail))) (chunk0046Push00 (chunk0045Push00 (chunk0044Push00 (acc)))) := array_chunk0046 fuel (chunk0047Chars00 ++ (tail)) (chunk0045Push00 (chunk0044Push00 (acc)))
    _ = SourceJson.array (fuel + 40) (SourceJson.white tail) (blockPush acc) := array_chunk0047 fuel (tail) (chunk0046Push00 (chunk0045Push00 (chunk0044Push00 (acc))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 209064).take 2758 = blockChars := by rfl

theorem block_original_split : sourceRest 209064 = blockChars ++ sourceRest 211822 := by
  calc
    sourceRest 209064 = (sourceRest 209064).take 2758 ++ (sourceRest 209064).drop 2758 :=
      (List.take_append_drop 2758 (sourceRest 209064)).symm
    _ = blockChars ++ (sourceRest 209064).drop 2758 :=
      congrArg (fun part => part ++ (sourceRest 209064).drop 2758) block_original_prefix
    _ = blockChars ++ sourceRest 211822 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 209064 2758)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 47) (SourceJson.white (sourceRest 209064)) acc =
      SourceJson.array (fuel + 40) (SourceJson.white (sourceRest 211822)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 47) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 211822) acc)

#print axioms array_fragment0210878_chunk_000
#print axioms array_fragment0210878_chunk_001
#print axioms array_fragment0210878_chunk_002
#print axioms array_fragment0210878_chunk_003
#print axioms value_fragment0210878
#print axioms object_fragment0210652_field_000
#print axioms object_fragment0210652_field_001
#print axioms object_fragment0210652_field_002
#print axioms object_fragment0210652_field_003_header
#print axioms object_fragment0210652_field_003
#print axioms object_fragment0210652_field_004
#print axioms value_fragment0210652
#print axioms array_chunk0044
#print axioms array_chunk0045
#print axioms array_chunk0046
#print axioms array_chunk0047_head
#print axioms array_chunk0047
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end FaceLedgerBlock015

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
