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

namespace FaceLedgerBlock013

noncomputable def fragment0204535Acc00000 : List SourceJson := []

noncomputable def fragment0204535Chunk000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0204535Chunk000Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '6']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3'])]) :: ((.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1'])]) :: (acc))

theorem array_fragment0204535_chunk_000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 16) (SourceJson.white (fragment0204535Chunk000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 14) (SourceJson.white tail) (fragment0204535Chunk000Push00 acc) := by
  rfl

noncomputable def fragment0204535Acc00100 : List SourceJson := fragment0204535Chunk000Push00 fragment0204535Acc00000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0204535_array_chunk_000"
  err.flush

noncomputable def fragment0204535Chunk001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0204535Chunk001Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '6']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4'])]) :: ((.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['8']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '6']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '4'])]) :: (acc))

theorem array_fragment0204535_chunk_001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 14) (SourceJson.white (fragment0204535Chunk001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 12) (SourceJson.white tail) (fragment0204535Chunk001Push00 acc) := by
  rfl

noncomputable def fragment0204535Acc00200 : List SourceJson := fragment0204535Chunk001Push00 fragment0204535Acc00100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0204535_array_chunk_001"
  err.flush

noncomputable def fragment0204535Chunk002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0204535Chunk002Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['3']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4'])]) :: ((.arr [.number (String.ofList ['1']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '6']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4'])]) :: (acc))

theorem array_fragment0204535_chunk_002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 12) (SourceJson.white (fragment0204535Chunk002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 10) (SourceJson.white tail) (fragment0204535Chunk002Push00 acc) := by
  rfl

noncomputable def fragment0204535Acc00300 : List SourceJson := fragment0204535Chunk002Push00 fragment0204535Acc00200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0204535_array_chunk_002"
  err.flush

noncomputable def fragment0204535Chunk003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']']
noncomputable def fragment0204535Chunk003Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1', '6']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4'])]) :: (acc)

theorem array_fragment0204535_chunk_003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 10) (SourceJson.white (fragment0204535Chunk003Chars00 ++ tail)) acc =
      .ok (.arr ((fragment0204535Chunk003Push00 acc).reverse), tail) := by
  rfl

noncomputable def fragment0204535Acc00400 : List SourceJson := fragment0204535Chunk003Push00 fragment0204535Acc00300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0204535_array_chunk_003"
  err.flush

noncomputable def fragment0204535Chars : List Char := '[' :: (fragment0204535Chunk000Chars00 ++ fragment0204535Chunk001Chars00 ++ fragment0204535Chunk002Chars00 ++ fragment0204535Chunk003Chars00)
noncomputable def fragment0204535Value : SourceJson := .arr (fragment0204535Acc00400.reverse)

theorem value_fragment0204535 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 17) (fragment0204535Chars ++ tail) =
      .ok (fragment0204535Value, tail) := by
  have hinput : fragment0204535Chars ++ tail = '[' :: (fragment0204535Chunk000Chars00 ++ (fragment0204535Chunk001Chars00 ++ (fragment0204535Chunk002Chars00 ++ (fragment0204535Chunk003Chars00 ++ (tail))))) := by
    simp only [fragment0204535Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 17) (fragment0204535Chars ++ tail) =
        SourceJson.value (fuel + 17) ('[' :: (fragment0204535Chunk000Chars00 ++ (fragment0204535Chunk001Chars00 ++ (fragment0204535Chunk002Chars00 ++ (fragment0204535Chunk003Chars00 ++ (tail)))))) :=
      congrArg (SourceJson.value (fuel + 17)) hinput
    _ = SourceJson.array (fuel + 16) (SourceJson.white (fragment0204535Chunk000Chars00 ++ (fragment0204535Chunk001Chars00 ++ (fragment0204535Chunk002Chars00 ++ (fragment0204535Chunk003Chars00 ++ (tail)))))) fragment0204535Acc00000 := by rfl
    _ = SourceJson.array (fuel + 14) (SourceJson.white (fragment0204535Chunk001Chars00 ++ (fragment0204535Chunk002Chars00 ++ (fragment0204535Chunk003Chars00 ++ (tail))))) fragment0204535Acc00100 := array_fragment0204535_chunk_000 fuel (fragment0204535Chunk001Chars00 ++ (fragment0204535Chunk002Chars00 ++ (fragment0204535Chunk003Chars00 ++ (tail)))) fragment0204535Acc00000
    _ = SourceJson.array (fuel + 12) (SourceJson.white (fragment0204535Chunk002Chars00 ++ (fragment0204535Chunk003Chars00 ++ (tail)))) fragment0204535Acc00200 := array_fragment0204535_chunk_001 fuel (fragment0204535Chunk002Chars00 ++ (fragment0204535Chunk003Chars00 ++ (tail))) fragment0204535Acc00100
    _ = SourceJson.array (fuel + 10) (SourceJson.white (fragment0204535Chunk003Chars00 ++ (tail))) fragment0204535Acc00300 := array_fragment0204535_chunk_002 fuel (fragment0204535Chunk003Chars00 ++ (tail)) fragment0204535Acc00200
    _ = .ok (fragment0204535Value, tail) := array_fragment0204535_chunk_003 fuel (tail) fragment0204535Acc00300

noncomputable def fragment0204312Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0204312Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0204312Field000Value00 : SourceJson := .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '6']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4'])]
noncomputable def fragment0204312Acc00100 : List (String × SourceJson) := (fragment0204312Field000Key00, fragment0204312Field000Value00) :: fragment0204312Acc00000
noncomputable def fragment0204312Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0204312_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 21) (SourceJson.white (fragment0204312Field000Chars00 ++ tail)) fragment0204312Acc00000 =
      SourceJson.object (fuel + 20) (SourceJson.white tail) fragment0204312Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0204312_object_field_000"
  err.flush

noncomputable def fragment0204312Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0204312Field001Value00 : SourceJson := .number (String.ofList ['5'])
noncomputable def fragment0204312Acc00200 : List (String × SourceJson) := (fragment0204312Field001Key00, fragment0204312Field001Value00) :: fragment0204312Acc00100
noncomputable def fragment0204312Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '5', ',']

theorem object_fragment0204312_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 20) (SourceJson.white (fragment0204312Field001Chars00 ++ tail)) fragment0204312Acc00100 =
      SourceJson.object (fuel + 19) (SourceJson.white tail) fragment0204312Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0204312_object_field_001"
  err.flush

noncomputable def fragment0204312Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0204312Field002Value00 : SourceJson := .number (String.ofList ['2', '4'])
noncomputable def fragment0204312Acc00300 : List (String × SourceJson) := (fragment0204312Field002Key00, fragment0204312Field002Value00) :: fragment0204312Acc00200
noncomputable def fragment0204312Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '2', '4', ',']

theorem object_fragment0204312_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 19) (SourceJson.white (fragment0204312Field002Chars00 ++ tail)) fragment0204312Acc00200 =
      SourceJson.object (fuel + 18) (SourceJson.white tail) fragment0204312Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0204312_object_field_002"
  err.flush

noncomputable def fragment0204312Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0204312Field003Value00 : SourceJson := fragment0204535Value
noncomputable def fragment0204312Acc00400 : List (String × SourceJson) := (fragment0204312Field003Key00, fragment0204312Field003Value00) :: fragment0204312Acc00300
noncomputable def fragment0204312Field003HeaderChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ']
noncomputable def fragment0204312Field003SuffixChars00 : List Char := [',']
noncomputable def fragment0204312Field003Chars00 : List Char := fragment0204312Field003HeaderChars00 ++ fragment0204535Chars ++ fragment0204312Field003SuffixChars00

noncomputable def fragment0204312Field003AfterValue00 (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending => .ok (.obj (((fragment0204312Field003Key00, result.1) :: fragment0204312Acc00300).reverse), ending)
  | ',' :: ending => SourceJson.object fuel (SourceJson.white ending) ((fragment0204312Field003Key00, result.1) :: fragment0204312Acc00300)
  | _ => .error "object separator missing"

theorem object_fragment0204312_field_003_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 18) (SourceJson.white (fragment0204312Field003HeaderChars00 ++ rest)) fragment0204312Acc00300 =
      (SourceJson.value (fuel + 17) rest).bind (fragment0204312Field003AfterValue00 (fuel + 17)) := by rfl

theorem object_fragment0204312_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 18) (SourceJson.white (fragment0204312Field003Chars00 ++ tail)) fragment0204312Acc00300 =
      SourceJson.object (fuel + 17) (SourceJson.white tail) fragment0204312Acc00400 := by
  have hinput : fragment0204312Field003Chars00 ++ tail = fragment0204312Field003HeaderChars00 ++ (fragment0204535Chars ++ (fragment0204312Field003SuffixChars00 ++ tail)) := by
    simp only [fragment0204312Field003Chars00, List.append_assoc]
  calc
    SourceJson.object (fuel + 18) (SourceJson.white (fragment0204312Field003Chars00 ++ tail)) fragment0204312Acc00300 =
        SourceJson.object (fuel + 18)
          (SourceJson.white (fragment0204312Field003HeaderChars00 ++ (fragment0204535Chars ++ (fragment0204312Field003SuffixChars00 ++ tail)))) fragment0204312Acc00300 :=
      congrArg (fun s => SourceJson.object (fuel + 18) (SourceJson.white s) fragment0204312Acc00300) hinput
    _ = (SourceJson.value (fuel + 17) (fragment0204535Chars ++ (fragment0204312Field003SuffixChars00 ++ tail))).bind
        (fragment0204312Field003AfterValue00 (fuel + 17)) := object_fragment0204312_field_003_header fuel (fragment0204535Chars ++ (fragment0204312Field003SuffixChars00 ++ tail))
    _ = (Except.ok (fragment0204535Value, fragment0204312Field003SuffixChars00 ++ tail)).bind (fragment0204312Field003AfterValue00 (fuel + 17)) :=
      congrArg (fun result => result.bind (fragment0204312Field003AfterValue00 (fuel + 17)))
        (value_fragment0204535 (fuel + 0) (fragment0204312Field003SuffixChars00 ++ tail))
    _ = SourceJson.object (fuel + 17) (SourceJson.white tail) fragment0204312Acc00400 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0204312_object_field_003"
  err.flush

noncomputable def fragment0204312Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0204312Field004Value00 : SourceJson := .number (String.ofList ['5'])
noncomputable def fragment0204312Acc00500 : List (String × SourceJson) := (fragment0204312Field004Key00, fragment0204312Field004Value00) :: fragment0204312Acc00400
noncomputable def fragment0204312Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '5', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0204312_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 17) (SourceJson.white (fragment0204312Field004Chars00 ++ tail)) fragment0204312Acc00400 =
      .ok (.obj (fragment0204312Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0204312_object_field_004"
  err.flush

noncomputable def fragment0204312Chars : List Char := '{' :: (fragment0204312Field000Chars00 ++ fragment0204312Field001Chars00 ++ fragment0204312Field002Chars00 ++ fragment0204312Field003Chars00 ++ fragment0204312Field004Chars00)
noncomputable def fragment0204312Value : SourceJson := .obj (fragment0204312Acc00500.reverse)

theorem value_fragment0204312 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 22) (fragment0204312Chars ++ tail) =
      .ok (fragment0204312Value, tail) := by
  have hinput : fragment0204312Chars ++ tail = '{' :: (fragment0204312Field000Chars00 ++ (fragment0204312Field001Chars00 ++ (fragment0204312Field002Chars00 ++ (fragment0204312Field003Chars00 ++ (fragment0204312Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0204312Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 22) (fragment0204312Chars ++ tail) =
        SourceJson.value (fuel + 22) ('{' :: (fragment0204312Field000Chars00 ++ (fragment0204312Field001Chars00 ++ (fragment0204312Field002Chars00 ++ (fragment0204312Field003Chars00 ++ (fragment0204312Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 22)) hinput
    _ = SourceJson.object (fuel + 21) (SourceJson.white (fragment0204312Field000Chars00 ++ (fragment0204312Field001Chars00 ++ (fragment0204312Field002Chars00 ++ (fragment0204312Field003Chars00 ++ (fragment0204312Field004Chars00 ++ (tail))))))) fragment0204312Acc00000 := by rfl
    _ = SourceJson.object (fuel + 20) (SourceJson.white (fragment0204312Field001Chars00 ++ (fragment0204312Field002Chars00 ++ (fragment0204312Field003Chars00 ++ (fragment0204312Field004Chars00 ++ (tail)))))) fragment0204312Acc00100 := object_fragment0204312_field_000 fuel (fragment0204312Field001Chars00 ++ (fragment0204312Field002Chars00 ++ (fragment0204312Field003Chars00 ++ (fragment0204312Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 19) (SourceJson.white (fragment0204312Field002Chars00 ++ (fragment0204312Field003Chars00 ++ (fragment0204312Field004Chars00 ++ (tail))))) fragment0204312Acc00200 := object_fragment0204312_field_001 fuel (fragment0204312Field002Chars00 ++ (fragment0204312Field003Chars00 ++ (fragment0204312Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 18) (SourceJson.white (fragment0204312Field003Chars00 ++ (fragment0204312Field004Chars00 ++ (tail)))) fragment0204312Acc00300 := object_fragment0204312_field_002 fuel (fragment0204312Field003Chars00 ++ (fragment0204312Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 17) (SourceJson.white (fragment0204312Field004Chars00 ++ (tail))) fragment0204312Acc00400 := object_fragment0204312_field_003 fuel (fragment0204312Field004Chars00 ++ (tail))
    _ = .ok (fragment0204312Value, tail) := object_fragment0204312_field_004 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0035_before_reader"
  err.flush

noncomputable def chunk0035Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '3', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0035Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['8']), .number (String.ofList ['1', '3']), .number (String.ofList ['2', '5'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['3'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['2', '5'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['1', '3'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['8'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['8']), .number (String.ofList ['1', '3']), .number (String.ofList ['2', '5'])], .arr [.number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['8']), .number (String.ofList ['2', '5'])], .arr [.number (String.ofList ['5']), .number (String.ofList ['1', '3']), .number (String.ofList ['2', '5'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['3']))]) :: (acc)

theorem array_chunk0035 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 58) (SourceJson.white (chunk0035Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 57) (SourceJson.white tail) (chunk0035Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0035_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0036_before_reader"
  err.flush

noncomputable def chunk0036Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '2', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0036Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['8'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['2'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['8'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['1']), .number (String.ofList ['3'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['8'])], .arr [.number (String.ofList ['3']), .number (String.ofList ['8'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['1']))]) :: ((.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['1', '3'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['2'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['1', '3'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['1']), .number (String.ofList ['3'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['1', '3'])], .arr [.number (String.ofList ['3']), .number (String.ofList ['5'])], .arr [.number (String.ofList ['5']), .number (String.ofList ['1', '3'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['2']))]) :: (acc))

theorem array_chunk0036 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 57) (SourceJson.white (chunk0036Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 55) (SourceJson.white tail) (chunk0036Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0036_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0037_before_reader"
  err.flush

noncomputable def chunk0037Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0037Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['8']), .number (String.ofList ['1', '0'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['3'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['1', '0'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['8'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['1', '0'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['8']), .number (String.ofList ['1', '0'])], .arr [.number (String.ofList ['3']), .number (String.ofList ['8']), .number (String.ofList ['1', '0'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['1']))]) :: (acc)

theorem array_chunk0037 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 55) (SourceJson.white (chunk0037Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 54) (SourceJson.white tail) (chunk0037Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0037_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0038_before_reader"
  err.flush

noncomputable def chunk0038Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0038Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['4'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['1', '1'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['8']), .number (String.ofList ['1', '0'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['8']), .number (String.ofList ['1', '1'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1'])], .arr [.number (String.ofList ['3']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['1']))]) :: (acc)

theorem array_chunk0038 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 54) (SourceJson.white (chunk0038Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 53) (SourceJson.white tail) (chunk0038Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0038_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0039_before_reader"
  err.flush

noncomputable def chunk0039LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0039SuffixChars00 : List Char := [',']
noncomputable def chunk0039Chars00 : List Char := chunk0039LeadChars00 ++ fragment0204312Chars ++ chunk0039SuffixChars00
noncomputable def chunk0039Push00 (acc : List SourceJson) : List SourceJson := fragment0204312Value :: acc

noncomputable def chunk0039AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0039_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 53)
      (SourceJson.white (chunk0039LeadChars00 ++ (fragment0204312Chars ++ rest))) acc =
      (SourceJson.value (fuel + 52) (fragment0204312Chars ++ rest)).bind
        (chunk0039AfterValue00 (fuel + 52) acc) := by rfl

theorem array_chunk0039 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 53) (SourceJson.white (chunk0039Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 52) (SourceJson.white tail) (chunk0039Push00 acc) := by
  have hinput : chunk0039Chars00 ++ tail = chunk0039LeadChars00 ++ (fragment0204312Chars ++ (chunk0039SuffixChars00 ++ tail)) := by
    simp only [chunk0039Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 53) (SourceJson.white (chunk0039Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 53)
          (SourceJson.white (chunk0039LeadChars00 ++ (fragment0204312Chars ++ (chunk0039SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 53) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 52) (fragment0204312Chars ++ (chunk0039SuffixChars00 ++ tail))).bind
        (chunk0039AfterValue00 (fuel + 52) acc) := array_chunk0039_head fuel (chunk0039SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0204312Value, chunk0039SuffixChars00 ++ tail)).bind
        (chunk0039AfterValue00 (fuel + 52) acc) :=
      congrArg (fun result => result.bind (chunk0039AfterValue00 (fuel + 52) acc))
        (value_fragment0204312 (fuel + 30) (chunk0039SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 52) (SourceJson.white tail) (chunk0039Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0039_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0035Chars00 ++ chunk0036Chars00 ++ chunk0037Chars00 ++ chunk0038Chars00 ++ chunk0039Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0039Push00 (chunk0038Push00 (chunk0037Push00 (chunk0036Push00 (chunk0035Push00 (acc)))))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 58) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 52) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0035Chars00 ++ (chunk0036Chars00 ++ (chunk0037Chars00 ++ (chunk0038Chars00 ++ (chunk0039Chars00 ++ (tail))))) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 58) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 58) (SourceJson.white (chunk0035Chars00 ++ (chunk0036Chars00 ++ (chunk0037Chars00 ++ (chunk0038Chars00 ++ (chunk0039Chars00 ++ (tail))))))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 58) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 57) (SourceJson.white (chunk0036Chars00 ++ (chunk0037Chars00 ++ (chunk0038Chars00 ++ (chunk0039Chars00 ++ (tail)))))) (chunk0035Push00 (acc)) := array_chunk0035 fuel (chunk0036Chars00 ++ (chunk0037Chars00 ++ (chunk0038Chars00 ++ (chunk0039Chars00 ++ (tail))))) (acc)
    _ = SourceJson.array (fuel + 55) (SourceJson.white (chunk0037Chars00 ++ (chunk0038Chars00 ++ (chunk0039Chars00 ++ (tail))))) (chunk0036Push00 (chunk0035Push00 (acc))) := array_chunk0036 fuel (chunk0037Chars00 ++ (chunk0038Chars00 ++ (chunk0039Chars00 ++ (tail)))) (chunk0035Push00 (acc))
    _ = SourceJson.array (fuel + 54) (SourceJson.white (chunk0038Chars00 ++ (chunk0039Chars00 ++ (tail)))) (chunk0037Push00 (chunk0036Push00 (chunk0035Push00 (acc)))) := array_chunk0037 fuel (chunk0038Chars00 ++ (chunk0039Chars00 ++ (tail))) (chunk0036Push00 (chunk0035Push00 (acc)))
    _ = SourceJson.array (fuel + 53) (SourceJson.white (chunk0039Chars00 ++ (tail))) (chunk0038Push00 (chunk0037Push00 (chunk0036Push00 (chunk0035Push00 (acc))))) := array_chunk0038 fuel (chunk0039Chars00 ++ (tail)) (chunk0037Push00 (chunk0036Push00 (chunk0035Push00 (acc))))
    _ = SourceJson.array (fuel + 52) (SourceJson.white tail) (blockPush acc) := array_chunk0039 fuel (tail) (chunk0038Push00 (chunk0037Push00 (chunk0036Push00 (chunk0035Push00 (acc)))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 201950).take 3514 = blockChars := by rfl

theorem block_original_split : sourceRest 201950 = blockChars ++ sourceRest 205464 := by
  calc
    sourceRest 201950 = (sourceRest 201950).take 3514 ++ (sourceRest 201950).drop 3514 :=
      (List.take_append_drop 3514 (sourceRest 201950)).symm
    _ = blockChars ++ (sourceRest 201950).drop 3514 :=
      congrArg (fun part => part ++ (sourceRest 201950).drop 3514) block_original_prefix
    _ = blockChars ++ sourceRest 205464 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 201950 3514)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 58) (SourceJson.white (sourceRest 201950)) acc =
      SourceJson.array (fuel + 52) (SourceJson.white (sourceRest 205464)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 58) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 205464) acc)

#print axioms array_fragment0204535_chunk_000
#print axioms array_fragment0204535_chunk_001
#print axioms array_fragment0204535_chunk_002
#print axioms array_fragment0204535_chunk_003
#print axioms value_fragment0204535
#print axioms object_fragment0204312_field_000
#print axioms object_fragment0204312_field_001
#print axioms object_fragment0204312_field_002
#print axioms object_fragment0204312_field_003_header
#print axioms object_fragment0204312_field_003
#print axioms object_fragment0204312_field_004
#print axioms value_fragment0204312
#print axioms array_chunk0035
#print axioms array_chunk0036
#print axioms array_chunk0037
#print axioms array_chunk0038
#print axioms array_chunk0039_head
#print axioms array_chunk0039
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end FaceLedgerBlock013

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
