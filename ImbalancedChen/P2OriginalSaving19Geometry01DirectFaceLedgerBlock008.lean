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

namespace FaceLedgerBlock008

noncomputable def fragment0185492Acc00000 : List SourceJson := []

noncomputable def fragment0185492Chunk000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0185492Chunk000Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['6']), .number (String.ofList ['9']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '7']), .number (String.ofList ['2', '7'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '7']), .number (String.ofList ['2', '6'])]) :: (acc))

theorem array_fragment0185492_chunk_000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 16) (SourceJson.white (fragment0185492Chunk000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 14) (SourceJson.white tail) (fragment0185492Chunk000Push00 acc) := by
  rfl

noncomputable def fragment0185492Acc00100 : List SourceJson := fragment0185492Chunk000Push00 fragment0185492Acc00000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0185492_array_chunk_000"
  err.flush

noncomputable def fragment0185492Chunk001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0185492Chunk001Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['9'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['7']), .number (String.ofList ['9']), .number (String.ofList ['1', '2']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '7'])]) :: (acc))

theorem array_fragment0185492_chunk_001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 14) (SourceJson.white (fragment0185492Chunk001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 12) (SourceJson.white tail) (fragment0185492Chunk001Push00 acc) := by
  rfl

noncomputable def fragment0185492Acc00200 : List SourceJson := fragment0185492Chunk001Push00 fragment0185492Acc00100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0185492_array_chunk_001"
  err.flush

noncomputable def fragment0185492Chunk002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0185492Chunk002Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['9']), .number (String.ofList ['1', '7']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '7'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['9']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '7']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '7'])]) :: (acc))

theorem array_fragment0185492_chunk_002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 12) (SourceJson.white (fragment0185492Chunk002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 10) (SourceJson.white tail) (fragment0185492Chunk002Push00 acc) := by
  rfl

noncomputable def fragment0185492Acc00300 : List SourceJson := fragment0185492Chunk002Push00 fragment0185492Acc00200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0185492_array_chunk_002"
  err.flush

noncomputable def fragment0185492Chunk003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']']
noncomputable def fragment0185492Chunk003Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['4']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '7']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '7'])]) :: (acc)

theorem array_fragment0185492_chunk_003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 10) (SourceJson.white (fragment0185492Chunk003Chars00 ++ tail)) acc =
      .ok (.arr ((fragment0185492Chunk003Push00 acc).reverse), tail) := by
  rfl

noncomputable def fragment0185492Acc00400 : List SourceJson := fragment0185492Chunk003Push00 fragment0185492Acc00300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0185492_array_chunk_003"
  err.flush

noncomputable def fragment0185492Chars : List Char := '[' :: (fragment0185492Chunk000Chars00 ++ fragment0185492Chunk001Chars00 ++ fragment0185492Chunk002Chars00 ++ fragment0185492Chunk003Chars00)
noncomputable def fragment0185492Value : SourceJson := .arr (fragment0185492Acc00400.reverse)

theorem value_fragment0185492 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 17) (fragment0185492Chars ++ tail) =
      .ok (fragment0185492Value, tail) := by
  have hinput : fragment0185492Chars ++ tail = '[' :: (fragment0185492Chunk000Chars00 ++ (fragment0185492Chunk001Chars00 ++ (fragment0185492Chunk002Chars00 ++ (fragment0185492Chunk003Chars00 ++ (tail))))) := by
    simp only [fragment0185492Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 17) (fragment0185492Chars ++ tail) =
        SourceJson.value (fuel + 17) ('[' :: (fragment0185492Chunk000Chars00 ++ (fragment0185492Chunk001Chars00 ++ (fragment0185492Chunk002Chars00 ++ (fragment0185492Chunk003Chars00 ++ (tail)))))) :=
      congrArg (SourceJson.value (fuel + 17)) hinput
    _ = SourceJson.array (fuel + 16) (SourceJson.white (fragment0185492Chunk000Chars00 ++ (fragment0185492Chunk001Chars00 ++ (fragment0185492Chunk002Chars00 ++ (fragment0185492Chunk003Chars00 ++ (tail)))))) fragment0185492Acc00000 := by rfl
    _ = SourceJson.array (fuel + 14) (SourceJson.white (fragment0185492Chunk001Chars00 ++ (fragment0185492Chunk002Chars00 ++ (fragment0185492Chunk003Chars00 ++ (tail))))) fragment0185492Acc00100 := array_fragment0185492_chunk_000 fuel (fragment0185492Chunk001Chars00 ++ (fragment0185492Chunk002Chars00 ++ (fragment0185492Chunk003Chars00 ++ (tail)))) fragment0185492Acc00000
    _ = SourceJson.array (fuel + 12) (SourceJson.white (fragment0185492Chunk002Chars00 ++ (fragment0185492Chunk003Chars00 ++ (tail)))) fragment0185492Acc00200 := array_fragment0185492_chunk_001 fuel (fragment0185492Chunk002Chars00 ++ (fragment0185492Chunk003Chars00 ++ (tail))) fragment0185492Acc00100
    _ = SourceJson.array (fuel + 10) (SourceJson.white (fragment0185492Chunk003Chars00 ++ (tail))) fragment0185492Acc00300 := array_fragment0185492_chunk_002 fuel (fragment0185492Chunk003Chars00 ++ (tail)) fragment0185492Acc00200
    _ = .ok (fragment0185492Value, tail) := array_fragment0185492_chunk_003 fuel (tail) fragment0185492Acc00300

noncomputable def fragment0185272Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0185272Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0185272Field000Value00 : SourceJson := .arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['9']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '7']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '7'])]
noncomputable def fragment0185272Acc00100 : List (String × SourceJson) := (fragment0185272Field000Key00, fragment0185272Field000Value00) :: fragment0185272Acc00000
noncomputable def fragment0185272Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0185272_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 21) (SourceJson.white (fragment0185272Field000Chars00 ++ tail)) fragment0185272Acc00000 =
      SourceJson.object (fuel + 20) (SourceJson.white tail) fragment0185272Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0185272_object_field_000"
  err.flush

noncomputable def fragment0185272Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0185272Field001Value00 : SourceJson := .number (String.ofList ['5'])
noncomputable def fragment0185272Acc00200 : List (String × SourceJson) := (fragment0185272Field001Key00, fragment0185272Field001Value00) :: fragment0185272Acc00100
noncomputable def fragment0185272Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '5', ',']

theorem object_fragment0185272_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 20) (SourceJson.white (fragment0185272Field001Chars00 ++ tail)) fragment0185272Acc00100 =
      SourceJson.object (fuel + 19) (SourceJson.white tail) fragment0185272Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0185272_object_field_001"
  err.flush

noncomputable def fragment0185272Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0185272Field002Value00 : SourceJson := .number (String.ofList ['2', '7'])
noncomputable def fragment0185272Acc00300 : List (String × SourceJson) := (fragment0185272Field002Key00, fragment0185272Field002Value00) :: fragment0185272Acc00200
noncomputable def fragment0185272Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '2', '7', ',']

theorem object_fragment0185272_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 19) (SourceJson.white (fragment0185272Field002Chars00 ++ tail)) fragment0185272Acc00200 =
      SourceJson.object (fuel + 18) (SourceJson.white tail) fragment0185272Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0185272_object_field_002"
  err.flush

noncomputable def fragment0185272Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0185272Field003Value00 : SourceJson := fragment0185492Value
noncomputable def fragment0185272Acc00400 : List (String × SourceJson) := (fragment0185272Field003Key00, fragment0185272Field003Value00) :: fragment0185272Acc00300
noncomputable def fragment0185272Field003HeaderChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ']
noncomputable def fragment0185272Field003SuffixChars00 : List Char := [',']
noncomputable def fragment0185272Field003Chars00 : List Char := fragment0185272Field003HeaderChars00 ++ fragment0185492Chars ++ fragment0185272Field003SuffixChars00

noncomputable def fragment0185272Field003AfterValue00 (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending => .ok (.obj (((fragment0185272Field003Key00, result.1) :: fragment0185272Acc00300).reverse), ending)
  | ',' :: ending => SourceJson.object fuel (SourceJson.white ending) ((fragment0185272Field003Key00, result.1) :: fragment0185272Acc00300)
  | _ => .error "object separator missing"

theorem object_fragment0185272_field_003_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 18) (SourceJson.white (fragment0185272Field003HeaderChars00 ++ rest)) fragment0185272Acc00300 =
      (SourceJson.value (fuel + 17) rest).bind (fragment0185272Field003AfterValue00 (fuel + 17)) := by rfl

theorem object_fragment0185272_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 18) (SourceJson.white (fragment0185272Field003Chars00 ++ tail)) fragment0185272Acc00300 =
      SourceJson.object (fuel + 17) (SourceJson.white tail) fragment0185272Acc00400 := by
  have hinput : fragment0185272Field003Chars00 ++ tail = fragment0185272Field003HeaderChars00 ++ (fragment0185492Chars ++ (fragment0185272Field003SuffixChars00 ++ tail)) := by
    simp only [fragment0185272Field003Chars00, List.append_assoc]
  calc
    SourceJson.object (fuel + 18) (SourceJson.white (fragment0185272Field003Chars00 ++ tail)) fragment0185272Acc00300 =
        SourceJson.object (fuel + 18)
          (SourceJson.white (fragment0185272Field003HeaderChars00 ++ (fragment0185492Chars ++ (fragment0185272Field003SuffixChars00 ++ tail)))) fragment0185272Acc00300 :=
      congrArg (fun s => SourceJson.object (fuel + 18) (SourceJson.white s) fragment0185272Acc00300) hinput
    _ = (SourceJson.value (fuel + 17) (fragment0185492Chars ++ (fragment0185272Field003SuffixChars00 ++ tail))).bind
        (fragment0185272Field003AfterValue00 (fuel + 17)) := object_fragment0185272_field_003_header fuel (fragment0185492Chars ++ (fragment0185272Field003SuffixChars00 ++ tail))
    _ = (Except.ok (fragment0185492Value, fragment0185272Field003SuffixChars00 ++ tail)).bind (fragment0185272Field003AfterValue00 (fuel + 17)) :=
      congrArg (fun result => result.bind (fragment0185272Field003AfterValue00 (fuel + 17)))
        (value_fragment0185492 (fuel + 0) (fragment0185272Field003SuffixChars00 ++ tail))
    _ = SourceJson.object (fuel + 17) (SourceJson.white tail) fragment0185272Acc00400 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0185272_object_field_003"
  err.flush

noncomputable def fragment0185272Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0185272Field004Value00 : SourceJson := .number (String.ofList ['5'])
noncomputable def fragment0185272Acc00500 : List (String × SourceJson) := (fragment0185272Field004Key00, fragment0185272Field004Value00) :: fragment0185272Acc00400
noncomputable def fragment0185272Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '5', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0185272_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 17) (SourceJson.white (fragment0185272Field004Chars00 ++ tail)) fragment0185272Acc00400 =
      .ok (.obj (fragment0185272Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0185272_object_field_004"
  err.flush

noncomputable def fragment0185272Chars : List Char := '{' :: (fragment0185272Field000Chars00 ++ fragment0185272Field001Chars00 ++ fragment0185272Field002Chars00 ++ fragment0185272Field003Chars00 ++ fragment0185272Field004Chars00)
noncomputable def fragment0185272Value : SourceJson := .obj (fragment0185272Acc00500.reverse)

theorem value_fragment0185272 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 22) (fragment0185272Chars ++ tail) =
      .ok (fragment0185272Value, tail) := by
  have hinput : fragment0185272Chars ++ tail = '{' :: (fragment0185272Field000Chars00 ++ (fragment0185272Field001Chars00 ++ (fragment0185272Field002Chars00 ++ (fragment0185272Field003Chars00 ++ (fragment0185272Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0185272Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 22) (fragment0185272Chars ++ tail) =
        SourceJson.value (fuel + 22) ('{' :: (fragment0185272Field000Chars00 ++ (fragment0185272Field001Chars00 ++ (fragment0185272Field002Chars00 ++ (fragment0185272Field003Chars00 ++ (fragment0185272Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 22)) hinput
    _ = SourceJson.object (fuel + 21) (SourceJson.white (fragment0185272Field000Chars00 ++ (fragment0185272Field001Chars00 ++ (fragment0185272Field002Chars00 ++ (fragment0185272Field003Chars00 ++ (fragment0185272Field004Chars00 ++ (tail))))))) fragment0185272Acc00000 := by rfl
    _ = SourceJson.object (fuel + 20) (SourceJson.white (fragment0185272Field001Chars00 ++ (fragment0185272Field002Chars00 ++ (fragment0185272Field003Chars00 ++ (fragment0185272Field004Chars00 ++ (tail)))))) fragment0185272Acc00100 := object_fragment0185272_field_000 fuel (fragment0185272Field001Chars00 ++ (fragment0185272Field002Chars00 ++ (fragment0185272Field003Chars00 ++ (fragment0185272Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 19) (SourceJson.white (fragment0185272Field002Chars00 ++ (fragment0185272Field003Chars00 ++ (fragment0185272Field004Chars00 ++ (tail))))) fragment0185272Acc00200 := object_fragment0185272_field_001 fuel (fragment0185272Field002Chars00 ++ (fragment0185272Field003Chars00 ++ (fragment0185272Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 18) (SourceJson.white (fragment0185272Field003Chars00 ++ (fragment0185272Field004Chars00 ++ (tail)))) fragment0185272Acc00300 := object_fragment0185272_field_002 fuel (fragment0185272Field003Chars00 ++ (fragment0185272Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 17) (SourceJson.white (fragment0185272Field004Chars00 ++ (tail))) fragment0185272Acc00400 := object_fragment0185272_field_003 fuel (fragment0185272Field004Chars00 ++ (tail))
    _ = .ok (fragment0185272Value, tail) := object_fragment0185272_field_004 fuel (tail)

noncomputable def fragment0186412Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0186412Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0186412Field000Value00 : SourceJson := .arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '7']), .number (String.ofList ['2', '6'])]
noncomputable def fragment0186412Acc00100 : List (String × SourceJson) := (fragment0186412Field000Key00, fragment0186412Field000Value00) :: fragment0186412Acc00000
noncomputable def fragment0186412Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0186412_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 18) (SourceJson.white (fragment0186412Field000Chars00 ++ tail)) fragment0186412Acc00000 =
      SourceJson.object (fuel + 17) (SourceJson.white tail) fragment0186412Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0186412_object_field_000"
  err.flush

noncomputable def fragment0186412Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0186412Field001Value00 : SourceJson := .number (String.ofList ['4'])
noncomputable def fragment0186412Acc00200 : List (String × SourceJson) := (fragment0186412Field001Key00, fragment0186412Field001Value00) :: fragment0186412Acc00100
noncomputable def fragment0186412Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '4', ',']

theorem object_fragment0186412_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 17) (SourceJson.white (fragment0186412Field001Chars00 ++ tail)) fragment0186412Acc00100 =
      SourceJson.object (fuel + 16) (SourceJson.white tail) fragment0186412Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0186412_object_field_001"
  err.flush

noncomputable def fragment0186412Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0186412Field002Value00 : SourceJson := .number (String.ofList ['2', '6'])
noncomputable def fragment0186412Acc00300 : List (String × SourceJson) := (fragment0186412Field002Key00, fragment0186412Field002Value00) :: fragment0186412Acc00200
noncomputable def fragment0186412Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '2', '6', ',']

theorem object_fragment0186412_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 16) (SourceJson.white (fragment0186412Field002Chars00 ++ tail)) fragment0186412Acc00200 =
      SourceJson.object (fuel + 15) (SourceJson.white tail) fragment0186412Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0186412_object_field_002"
  err.flush

noncomputable def fragment0186412Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0186412Field003Value00 : SourceJson := .arr [.arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['6']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '7'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['7']), .number (String.ofList ['1', '2']), .number (String.ofList ['2', '6'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['6']), .number (String.ofList ['7'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '7']), .number (String.ofList ['2', '6'])], .arr [.number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['1', '7']), .number (String.ofList ['2', '6'])], .arr [.number (String.ofList ['4']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '7']), .number (String.ofList ['2', '6'])]]
noncomputable def fragment0186412Acc00400 : List (String × SourceJson) := (fragment0186412Field003Key00, fragment0186412Field003Value00) :: fragment0186412Acc00300
noncomputable def fragment0186412Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0186412_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 15) (SourceJson.white (fragment0186412Field003Chars00 ++ tail)) fragment0186412Acc00300 =
      SourceJson.object (fuel + 14) (SourceJson.white tail) fragment0186412Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0186412_object_field_003"
  err.flush

noncomputable def fragment0186412Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0186412Field004Value00 : SourceJson := .number (String.ofList ['4'])
noncomputable def fragment0186412Acc00500 : List (String × SourceJson) := (fragment0186412Field004Key00, fragment0186412Field004Value00) :: fragment0186412Acc00400
noncomputable def fragment0186412Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0186412_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 14) (SourceJson.white (fragment0186412Field004Chars00 ++ tail)) fragment0186412Acc00400 =
      .ok (.obj (fragment0186412Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0186412_object_field_004"
  err.flush

noncomputable def fragment0186412Chars : List Char := '{' :: (fragment0186412Field000Chars00 ++ fragment0186412Field001Chars00 ++ fragment0186412Field002Chars00 ++ fragment0186412Field003Chars00 ++ fragment0186412Field004Chars00)
noncomputable def fragment0186412Value : SourceJson := .obj (fragment0186412Acc00500.reverse)

theorem value_fragment0186412 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 19) (fragment0186412Chars ++ tail) =
      .ok (fragment0186412Value, tail) := by
  have hinput : fragment0186412Chars ++ tail = '{' :: (fragment0186412Field000Chars00 ++ (fragment0186412Field001Chars00 ++ (fragment0186412Field002Chars00 ++ (fragment0186412Field003Chars00 ++ (fragment0186412Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0186412Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 19) (fragment0186412Chars ++ tail) =
        SourceJson.value (fuel + 19) ('{' :: (fragment0186412Field000Chars00 ++ (fragment0186412Field001Chars00 ++ (fragment0186412Field002Chars00 ++ (fragment0186412Field003Chars00 ++ (fragment0186412Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 19)) hinput
    _ = SourceJson.object (fuel + 18) (SourceJson.white (fragment0186412Field000Chars00 ++ (fragment0186412Field001Chars00 ++ (fragment0186412Field002Chars00 ++ (fragment0186412Field003Chars00 ++ (fragment0186412Field004Chars00 ++ (tail))))))) fragment0186412Acc00000 := by rfl
    _ = SourceJson.object (fuel + 17) (SourceJson.white (fragment0186412Field001Chars00 ++ (fragment0186412Field002Chars00 ++ (fragment0186412Field003Chars00 ++ (fragment0186412Field004Chars00 ++ (tail)))))) fragment0186412Acc00100 := object_fragment0186412_field_000 fuel (fragment0186412Field001Chars00 ++ (fragment0186412Field002Chars00 ++ (fragment0186412Field003Chars00 ++ (fragment0186412Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 16) (SourceJson.white (fragment0186412Field002Chars00 ++ (fragment0186412Field003Chars00 ++ (fragment0186412Field004Chars00 ++ (tail))))) fragment0186412Acc00200 := object_fragment0186412_field_001 fuel (fragment0186412Field002Chars00 ++ (fragment0186412Field003Chars00 ++ (fragment0186412Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 15) (SourceJson.white (fragment0186412Field003Chars00 ++ (fragment0186412Field004Chars00 ++ (tail)))) fragment0186412Acc00300 := object_fragment0186412_field_002 fuel (fragment0186412Field003Chars00 ++ (fragment0186412Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 14) (SourceJson.white (fragment0186412Field004Chars00 ++ (tail))) fragment0186412Acc00400 := object_fragment0186412_field_003 fuel (fragment0186412Field004Chars00 ++ (tail))
    _ = .ok (fragment0186412Value, tail) := object_fragment0186412_field_004 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0014_before_reader"
  err.flush

noncomputable def chunk0014Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '6', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0014Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['3'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['2', '0'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '9'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['1', '6']), .number (String.ofList ['2', '0'])], .arr [.number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0'])], .arr [.number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['6']))]) :: (acc)

theorem array_chunk0014 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 84) (SourceJson.white (chunk0014Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 83) (SourceJson.white tail) (chunk0014Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0014_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0015_before_reader"
  err.flush

noncomputable def chunk0015Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '2', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0015Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['0']), .number (String.ofList ['2'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['1'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['2'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['0'])], .arr [.number (String.ofList ['2'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['1']))]) :: ((.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['2'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['1', '6'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['0']), .number (String.ofList ['1'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['1', '5'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['1', '6'])], .arr [.number (String.ofList ['1', '5']), .number (String.ofList ['1', '6'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['2']))]) :: (acc))

theorem array_chunk0015 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 83) (SourceJson.white (chunk0015Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 81) (SourceJson.white tail) (chunk0015Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0015_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0016_before_reader"
  err.flush

noncomputable def chunk0016LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0016SuffixChars00 : List Char := [',']
noncomputable def chunk0016Chars00 : List Char := chunk0016LeadChars00 ++ fragment0185272Chars ++ chunk0016SuffixChars00
noncomputable def chunk0016Push00 (acc : List SourceJson) : List SourceJson := fragment0185272Value :: acc

noncomputable def chunk0016AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0016_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 81)
      (SourceJson.white (chunk0016LeadChars00 ++ (fragment0185272Chars ++ rest))) acc =
      (SourceJson.value (fuel + 80) (fragment0185272Chars ++ rest)).bind
        (chunk0016AfterValue00 (fuel + 80) acc) := by rfl

theorem array_chunk0016 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 81) (SourceJson.white (chunk0016Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 80) (SourceJson.white tail) (chunk0016Push00 acc) := by
  have hinput : chunk0016Chars00 ++ tail = chunk0016LeadChars00 ++ (fragment0185272Chars ++ (chunk0016SuffixChars00 ++ tail)) := by
    simp only [chunk0016Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 81) (SourceJson.white (chunk0016Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 81)
          (SourceJson.white (chunk0016LeadChars00 ++ (fragment0185272Chars ++ (chunk0016SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 81) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 80) (fragment0185272Chars ++ (chunk0016SuffixChars00 ++ tail))).bind
        (chunk0016AfterValue00 (fuel + 80) acc) := array_chunk0016_head fuel (chunk0016SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0185272Value, chunk0016SuffixChars00 ++ tail)).bind
        (chunk0016AfterValue00 (fuel + 80) acc) :=
      congrArg (fun result => result.bind (chunk0016AfterValue00 (fuel + 80) acc))
        (value_fragment0185272 (fuel + 58) (chunk0016SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 80) (SourceJson.white tail) (chunk0016Push00 acc) := by rfl

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
noncomputable def chunk0017Chars00 : List Char := chunk0017LeadChars00 ++ fragment0186412Chars ++ chunk0017SuffixChars00
noncomputable def chunk0017Push00 (acc : List SourceJson) : List SourceJson := fragment0186412Value :: acc

noncomputable def chunk0017AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0017_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 80)
      (SourceJson.white (chunk0017LeadChars00 ++ (fragment0186412Chars ++ rest))) acc =
      (SourceJson.value (fuel + 79) (fragment0186412Chars ++ rest)).bind
        (chunk0017AfterValue00 (fuel + 79) acc) := by rfl

theorem array_chunk0017 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 80) (SourceJson.white (chunk0017Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 79) (SourceJson.white tail) (chunk0017Push00 acc) := by
  have hinput : chunk0017Chars00 ++ tail = chunk0017LeadChars00 ++ (fragment0186412Chars ++ (chunk0017SuffixChars00 ++ tail)) := by
    simp only [chunk0017Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 80) (SourceJson.white (chunk0017Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 80)
          (SourceJson.white (chunk0017LeadChars00 ++ (fragment0186412Chars ++ (chunk0017SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 80) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 79) (fragment0186412Chars ++ (chunk0017SuffixChars00 ++ tail))).bind
        (chunk0017AfterValue00 (fuel + 79) acc) := array_chunk0017_head fuel (chunk0017SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0186412Value, chunk0017SuffixChars00 ++ tail)).bind
        (chunk0017AfterValue00 (fuel + 79) acc) :=
      congrArg (fun result => result.bind (chunk0017AfterValue00 (fuel + 79) acc))
        (value_fragment0186412 (fuel + 60) (chunk0017SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 79) (SourceJson.white tail) (chunk0017Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0017_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0018_before_reader"
  err.flush

noncomputable def chunk0018Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '3', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0018Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['6']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '7'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['3'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['1', '7'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['1', '2'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['6'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['6']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '7'])], .arr [.number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['6']), .number (String.ofList ['1', '7'])], .arr [.number (String.ofList ['4']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '7'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['3']))]) :: (acc)

theorem array_chunk0018 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 79) (SourceJson.white (chunk0018Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 78) (SourceJson.white tail) (chunk0018Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0018_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0014Chars00 ++ chunk0015Chars00 ++ chunk0016Chars00 ++ chunk0017Chars00 ++ chunk0018Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0018Push00 (chunk0017Push00 (chunk0016Push00 (chunk0015Push00 (chunk0014Push00 (acc)))))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 84) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 78) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0014Chars00 ++ (chunk0015Chars00 ++ (chunk0016Chars00 ++ (chunk0017Chars00 ++ (chunk0018Chars00 ++ (tail))))) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 84) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 84) (SourceJson.white (chunk0014Chars00 ++ (chunk0015Chars00 ++ (chunk0016Chars00 ++ (chunk0017Chars00 ++ (chunk0018Chars00 ++ (tail))))))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 84) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 83) (SourceJson.white (chunk0015Chars00 ++ (chunk0016Chars00 ++ (chunk0017Chars00 ++ (chunk0018Chars00 ++ (tail)))))) (chunk0014Push00 (acc)) := array_chunk0014 fuel (chunk0015Chars00 ++ (chunk0016Chars00 ++ (chunk0017Chars00 ++ (chunk0018Chars00 ++ (tail))))) (acc)
    _ = SourceJson.array (fuel + 81) (SourceJson.white (chunk0016Chars00 ++ (chunk0017Chars00 ++ (chunk0018Chars00 ++ (tail))))) (chunk0015Push00 (chunk0014Push00 (acc))) := array_chunk0015 fuel (chunk0016Chars00 ++ (chunk0017Chars00 ++ (chunk0018Chars00 ++ (tail)))) (chunk0014Push00 (acc))
    _ = SourceJson.array (fuel + 80) (SourceJson.white (chunk0017Chars00 ++ (chunk0018Chars00 ++ (tail)))) (chunk0016Push00 (chunk0015Push00 (chunk0014Push00 (acc)))) := array_chunk0016 fuel (chunk0017Chars00 ++ (chunk0018Chars00 ++ (tail))) (chunk0015Push00 (chunk0014Push00 (acc)))
    _ = SourceJson.array (fuel + 79) (SourceJson.white (chunk0018Chars00 ++ (tail))) (chunk0017Push00 (chunk0016Push00 (chunk0015Push00 (chunk0014Push00 (acc))))) := array_chunk0017 fuel (chunk0018Chars00 ++ (tail)) (chunk0016Push00 (chunk0015Push00 (chunk0014Push00 (acc))))
    _ = SourceJson.array (fuel + 78) (SourceJson.white tail) (blockPush acc) := array_chunk0018 fuel (tail) (chunk0017Push00 (chunk0016Push00 (chunk0015Push00 (chunk0014Push00 (acc)))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 183911).take 3912 = blockChars := by rfl

theorem block_original_split : sourceRest 183911 = blockChars ++ sourceRest 187823 := by
  calc
    sourceRest 183911 = (sourceRest 183911).take 3912 ++ (sourceRest 183911).drop 3912 :=
      (List.take_append_drop 3912 (sourceRest 183911)).symm
    _ = blockChars ++ (sourceRest 183911).drop 3912 :=
      congrArg (fun part => part ++ (sourceRest 183911).drop 3912) block_original_prefix
    _ = blockChars ++ sourceRest 187823 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 183911 3912)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 84) (SourceJson.white (sourceRest 183911)) acc =
      SourceJson.array (fuel + 78) (SourceJson.white (sourceRest 187823)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 84) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 187823) acc)

#print axioms array_fragment0185492_chunk_000
#print axioms array_fragment0185492_chunk_001
#print axioms array_fragment0185492_chunk_002
#print axioms array_fragment0185492_chunk_003
#print axioms value_fragment0185492
#print axioms object_fragment0185272_field_000
#print axioms object_fragment0185272_field_001
#print axioms object_fragment0185272_field_002
#print axioms object_fragment0185272_field_003_header
#print axioms object_fragment0185272_field_003
#print axioms object_fragment0185272_field_004
#print axioms value_fragment0185272
#print axioms object_fragment0186412_field_000
#print axioms object_fragment0186412_field_001
#print axioms object_fragment0186412_field_002
#print axioms object_fragment0186412_field_003
#print axioms object_fragment0186412_field_004
#print axioms value_fragment0186412
#print axioms array_chunk0014
#print axioms array_chunk0015
#print axioms array_chunk0016_head
#print axioms array_chunk0016
#print axioms array_chunk0017_head
#print axioms array_chunk0017
#print axioms array_chunk0018
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end FaceLedgerBlock008

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
