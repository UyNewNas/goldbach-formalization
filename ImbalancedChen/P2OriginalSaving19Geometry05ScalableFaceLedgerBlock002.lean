import ImbalancedChen.P2OriginalSaving19Geometry05ScalableInput

/-! Original face_ledger grouped chunk transitions, including exact compact-input binding.
The original packed input, original parser and original decoder are unchanged.
This is a source-only candidate until normal, kernel and full-owned checks pass. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

namespace FaceLedgerBlock002

noncomputable def fragment0089091Acc00000 : List SourceJson := []

noncomputable def fragment0089091Chunk000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0089091Chunk000Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['6']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '8']), .number (String.ofList ['2', '0'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['6']), .number (String.ofList ['1', '1'])]) :: (acc))

theorem array_fragment0089091_chunk_000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 16) (SourceJson.white (fragment0089091Chunk000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 14) (SourceJson.white tail) (fragment0089091Chunk000Push00 acc) := by
  rfl

noncomputable def fragment0089091Acc00100 : List SourceJson := fragment0089091Chunk000Push00 fragment0089091Acc00000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0089091_array_chunk_000"
  err.flush

noncomputable def fragment0089091Chunk001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0089091Chunk001Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['6']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '8']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '2'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '6']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '2'])]) :: (acc))

theorem array_fragment0089091_chunk_001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 14) (SourceJson.white (fragment0089091Chunk001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 12) (SourceJson.white tail) (fragment0089091Chunk001Push00 acc) := by
  rfl

noncomputable def fragment0089091Acc00200 : List SourceJson := fragment0089091Chunk001Push00 fragment0089091Acc00100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0089091_array_chunk_001"
  err.flush

noncomputable def fragment0089091Chunk002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0089091Chunk002Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['6']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '8']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '2'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['4']), .number (String.ofList ['6']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '8']), .number (String.ofList ['2', '2'])]) :: (acc))

theorem array_fragment0089091_chunk_002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 12) (SourceJson.white (fragment0089091Chunk002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 10) (SourceJson.white tail) (fragment0089091Chunk002Push00 acc) := by
  rfl

noncomputable def fragment0089091Acc00300 : List SourceJson := fragment0089091Chunk002Push00 fragment0089091Acc00200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0089091_array_chunk_002"
  err.flush

noncomputable def fragment0089091Chunk003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']']
noncomputable def fragment0089091Chunk003Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1', '4']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '8']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '2'])]) :: (acc)

theorem array_fragment0089091_chunk_003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 10) (SourceJson.white (fragment0089091Chunk003Chars00 ++ tail)) acc =
      .ok (.arr ((fragment0089091Chunk003Push00 acc).reverse), tail) := by
  rfl

noncomputable def fragment0089091Acc00400 : List SourceJson := fragment0089091Chunk003Push00 fragment0089091Acc00300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0089091_array_chunk_003"
  err.flush

noncomputable def fragment0089091Chars : List Char := '[' :: (fragment0089091Chunk000Chars00 ++ fragment0089091Chunk001Chars00 ++ fragment0089091Chunk002Chars00 ++ fragment0089091Chunk003Chars00)
noncomputable def fragment0089091Value : SourceJson := .arr (fragment0089091Acc00400.reverse)

theorem value_fragment0089091 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 17) (fragment0089091Chars ++ tail) =
      .ok (fragment0089091Value, tail) := by
  have hinput : fragment0089091Chars ++ tail = '[' :: (fragment0089091Chunk000Chars00 ++ (fragment0089091Chunk001Chars00 ++ (fragment0089091Chunk002Chars00 ++ (fragment0089091Chunk003Chars00 ++ (tail))))) := by
    simp only [fragment0089091Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 17) (fragment0089091Chars ++ tail) =
        SourceJson.value (fuel + 17) ('[' :: (fragment0089091Chunk000Chars00 ++ (fragment0089091Chunk001Chars00 ++ (fragment0089091Chunk002Chars00 ++ (fragment0089091Chunk003Chars00 ++ (tail)))))) :=
      congrArg (SourceJson.value (fuel + 17)) hinput
    _ = SourceJson.array (fuel + 16) (SourceJson.white (fragment0089091Chunk000Chars00 ++ (fragment0089091Chunk001Chars00 ++ (fragment0089091Chunk002Chars00 ++ (fragment0089091Chunk003Chars00 ++ (tail)))))) fragment0089091Acc00000 := by rfl
    _ = SourceJson.array (fuel + 14) (SourceJson.white (fragment0089091Chunk001Chars00 ++ (fragment0089091Chunk002Chars00 ++ (fragment0089091Chunk003Chars00 ++ (tail))))) fragment0089091Acc00100 := array_fragment0089091_chunk_000 fuel (fragment0089091Chunk001Chars00 ++ (fragment0089091Chunk002Chars00 ++ (fragment0089091Chunk003Chars00 ++ (tail)))) fragment0089091Acc00000
    _ = SourceJson.array (fuel + 12) (SourceJson.white (fragment0089091Chunk002Chars00 ++ (fragment0089091Chunk003Chars00 ++ (tail)))) fragment0089091Acc00200 := array_fragment0089091_chunk_001 fuel (fragment0089091Chunk002Chars00 ++ (fragment0089091Chunk003Chars00 ++ (tail))) fragment0089091Acc00100
    _ = SourceJson.array (fuel + 10) (SourceJson.white (fragment0089091Chunk003Chars00 ++ (tail))) fragment0089091Acc00300 := array_fragment0089091_chunk_002 fuel (fragment0089091Chunk003Chars00 ++ (tail)) fragment0089091Acc00200
    _ = .ok (fragment0089091Value, tail) := array_fragment0089091_chunk_003 fuel (tail) fragment0089091Acc00300

noncomputable def fragment0088869Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0088869Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0088869Field000Value00 : SourceJson := .arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['6']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '8']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '2'])]
noncomputable def fragment0088869Acc00100 : List (String × SourceJson) := (fragment0088869Field000Key00, fragment0088869Field000Value00) :: fragment0088869Acc00000
noncomputable def fragment0088869Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0088869_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 21) (SourceJson.white (fragment0088869Field000Chars00 ++ tail)) fragment0088869Acc00000 =
      SourceJson.object (fuel + 20) (SourceJson.white tail) fragment0088869Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0088869_object_field_000"
  err.flush

noncomputable def fragment0088869Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0088869Field001Value00 : SourceJson := .number (String.ofList ['5'])
noncomputable def fragment0088869Acc00200 : List (String × SourceJson) := (fragment0088869Field001Key00, fragment0088869Field001Value00) :: fragment0088869Acc00100
noncomputable def fragment0088869Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '5', ',']

theorem object_fragment0088869_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 20) (SourceJson.white (fragment0088869Field001Chars00 ++ tail)) fragment0088869Acc00100 =
      SourceJson.object (fuel + 19) (SourceJson.white tail) fragment0088869Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0088869_object_field_001"
  err.flush

noncomputable def fragment0088869Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0088869Field002Value00 : SourceJson := .number (String.ofList ['2', '2'])
noncomputable def fragment0088869Acc00300 : List (String × SourceJson) := (fragment0088869Field002Key00, fragment0088869Field002Value00) :: fragment0088869Acc00200
noncomputable def fragment0088869Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '2', '2', ',']

theorem object_fragment0088869_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 19) (SourceJson.white (fragment0088869Field002Chars00 ++ tail)) fragment0088869Acc00200 =
      SourceJson.object (fuel + 18) (SourceJson.white tail) fragment0088869Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0088869_object_field_002"
  err.flush

noncomputable def fragment0088869Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0088869Field003Value00 : SourceJson := fragment0089091Value
noncomputable def fragment0088869Acc00400 : List (String × SourceJson) := (fragment0088869Field003Key00, fragment0088869Field003Value00) :: fragment0088869Acc00300
noncomputable def fragment0088869Field003HeaderChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ']
noncomputable def fragment0088869Field003SuffixChars00 : List Char := [',']
noncomputable def fragment0088869Field003Chars00 : List Char := fragment0088869Field003HeaderChars00 ++ fragment0089091Chars ++ fragment0088869Field003SuffixChars00

noncomputable def fragment0088869Field003AfterValue00 (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending => .ok (.obj (((fragment0088869Field003Key00, result.1) :: fragment0088869Acc00300).reverse), ending)
  | ',' :: ending => SourceJson.object fuel (SourceJson.white ending) ((fragment0088869Field003Key00, result.1) :: fragment0088869Acc00300)
  | _ => .error "object separator missing"

theorem object_fragment0088869_field_003_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 18) (SourceJson.white (fragment0088869Field003HeaderChars00 ++ rest)) fragment0088869Acc00300 =
      (SourceJson.value (fuel + 17) rest).bind (fragment0088869Field003AfterValue00 (fuel + 17)) := by rfl

theorem object_fragment0088869_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 18) (SourceJson.white (fragment0088869Field003Chars00 ++ tail)) fragment0088869Acc00300 =
      SourceJson.object (fuel + 17) (SourceJson.white tail) fragment0088869Acc00400 := by
  have hinput : fragment0088869Field003Chars00 ++ tail = fragment0088869Field003HeaderChars00 ++ (fragment0089091Chars ++ (fragment0088869Field003SuffixChars00 ++ tail)) := by
    simp only [fragment0088869Field003Chars00, List.append_assoc]
  calc
    SourceJson.object (fuel + 18) (SourceJson.white (fragment0088869Field003Chars00 ++ tail)) fragment0088869Acc00300 =
        SourceJson.object (fuel + 18)
          (SourceJson.white (fragment0088869Field003HeaderChars00 ++ (fragment0089091Chars ++ (fragment0088869Field003SuffixChars00 ++ tail)))) fragment0088869Acc00300 :=
      congrArg (fun s => SourceJson.object (fuel + 18) (SourceJson.white s) fragment0088869Acc00300) hinput
    _ = (SourceJson.value (fuel + 17) (fragment0089091Chars ++ (fragment0088869Field003SuffixChars00 ++ tail))).bind
        (fragment0088869Field003AfterValue00 (fuel + 17)) := object_fragment0088869_field_003_header fuel (fragment0089091Chars ++ (fragment0088869Field003SuffixChars00 ++ tail))
    _ = (Except.ok (fragment0089091Value, fragment0088869Field003SuffixChars00 ++ tail)).bind (fragment0088869Field003AfterValue00 (fuel + 17)) :=
      congrArg (fun result => result.bind (fragment0088869Field003AfterValue00 (fuel + 17)))
        (value_fragment0089091 (fuel + 0) (fragment0088869Field003SuffixChars00 ++ tail))
    _ = SourceJson.object (fuel + 17) (SourceJson.white tail) fragment0088869Acc00400 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0088869_object_field_003"
  err.flush

noncomputable def fragment0088869Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0088869Field004Value00 : SourceJson := .number (String.ofList ['5'])
noncomputable def fragment0088869Acc00500 : List (String × SourceJson) := (fragment0088869Field004Key00, fragment0088869Field004Value00) :: fragment0088869Acc00400
noncomputable def fragment0088869Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '5', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0088869_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 17) (SourceJson.white (fragment0088869Field004Chars00 ++ tail)) fragment0088869Acc00400 =
      .ok (.obj (fragment0088869Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0088869_object_field_004"
  err.flush

noncomputable def fragment0088869Chars : List Char := '{' :: (fragment0088869Field000Chars00 ++ fragment0088869Field001Chars00 ++ fragment0088869Field002Chars00 ++ fragment0088869Field003Chars00 ++ fragment0088869Field004Chars00)
noncomputable def fragment0088869Value : SourceJson := .obj (fragment0088869Acc00500.reverse)

theorem value_fragment0088869 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 22) (fragment0088869Chars ++ tail) =
      .ok (fragment0088869Value, tail) := by
  have hinput : fragment0088869Chars ++ tail = '{' :: (fragment0088869Field000Chars00 ++ (fragment0088869Field001Chars00 ++ (fragment0088869Field002Chars00 ++ (fragment0088869Field003Chars00 ++ (fragment0088869Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0088869Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 22) (fragment0088869Chars ++ tail) =
        SourceJson.value (fuel + 22) ('{' :: (fragment0088869Field000Chars00 ++ (fragment0088869Field001Chars00 ++ (fragment0088869Field002Chars00 ++ (fragment0088869Field003Chars00 ++ (fragment0088869Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 22)) hinput
    _ = SourceJson.object (fuel + 21) (SourceJson.white (fragment0088869Field000Chars00 ++ (fragment0088869Field001Chars00 ++ (fragment0088869Field002Chars00 ++ (fragment0088869Field003Chars00 ++ (fragment0088869Field004Chars00 ++ (tail))))))) fragment0088869Acc00000 := by rfl
    _ = SourceJson.object (fuel + 20) (SourceJson.white (fragment0088869Field001Chars00 ++ (fragment0088869Field002Chars00 ++ (fragment0088869Field003Chars00 ++ (fragment0088869Field004Chars00 ++ (tail)))))) fragment0088869Acc00100 := object_fragment0088869_field_000 fuel (fragment0088869Field001Chars00 ++ (fragment0088869Field002Chars00 ++ (fragment0088869Field003Chars00 ++ (fragment0088869Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 19) (SourceJson.white (fragment0088869Field002Chars00 ++ (fragment0088869Field003Chars00 ++ (fragment0088869Field004Chars00 ++ (tail))))) fragment0088869Acc00200 := object_fragment0088869_field_001 fuel (fragment0088869Field002Chars00 ++ (fragment0088869Field003Chars00 ++ (fragment0088869Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 18) (SourceJson.white (fragment0088869Field003Chars00 ++ (fragment0088869Field004Chars00 ++ (tail)))) fragment0088869Acc00300 := object_fragment0088869_field_002 fuel (fragment0088869Field003Chars00 ++ (fragment0088869Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 17) (SourceJson.white (fragment0088869Field004Chars00 ++ (tail))) fragment0088869Acc00400 := object_fragment0088869_field_003 fuel (fragment0088869Field004Chars00 ++ (tail))
    _ = .ok (fragment0088869Value, tail) := object_fragment0088869_field_004 fuel (tail)

noncomputable def fragment0090021Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0090021Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0090021Field000Value00 : SourceJson := .arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['6']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '8']), .number (String.ofList ['2', '0'])]
noncomputable def fragment0090021Acc00100 : List (String × SourceJson) := (fragment0090021Field000Key00, fragment0090021Field000Value00) :: fragment0090021Acc00000
noncomputable def fragment0090021Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0090021_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 18) (SourceJson.white (fragment0090021Field000Chars00 ++ tail)) fragment0090021Acc00000 =
      SourceJson.object (fuel + 17) (SourceJson.white tail) fragment0090021Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0090021_object_field_000"
  err.flush

noncomputable def fragment0090021Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0090021Field001Value00 : SourceJson := .number (String.ofList ['4'])
noncomputable def fragment0090021Acc00200 : List (String × SourceJson) := (fragment0090021Field001Key00, fragment0090021Field001Value00) :: fragment0090021Acc00100
noncomputable def fragment0090021Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '4', ',']

theorem object_fragment0090021_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 17) (SourceJson.white (fragment0090021Field001Chars00 ++ tail)) fragment0090021Acc00100 =
      SourceJson.object (fuel + 16) (SourceJson.white tail) fragment0090021Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0090021_object_field_001"
  err.flush

noncomputable def fragment0090021Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0090021Field002Value00 : SourceJson := .number (String.ofList ['2', '0'])
noncomputable def fragment0090021Acc00300 : List (String × SourceJson) := (fragment0090021Field002Key00, fragment0090021Field002Value00) :: fragment0090021Acc00200
noncomputable def fragment0090021Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '2', '0', ',']

theorem object_fragment0090021_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 16) (SourceJson.white (fragment0090021Field002Chars00 ++ tail)) fragment0090021Acc00200 =
      SourceJson.object (fuel + 15) (SourceJson.white tail) fragment0090021Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0090021_object_field_002"
  err.flush

noncomputable def fragment0090021Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0090021Field003Value00 : SourceJson := .arr [.arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['6'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '6']), .number (String.ofList ['2', '0'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['6']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '8']), .number (String.ofList ['2', '0'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['4']), .number (String.ofList ['6']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '8'])], .arr [.number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['6']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '8']), .number (String.ofList ['2', '0'])], .arr [.number (String.ofList ['1', '4']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '8']), .number (String.ofList ['2', '0'])]]
noncomputable def fragment0090021Acc00400 : List (String × SourceJson) := (fragment0090021Field003Key00, fragment0090021Field003Value00) :: fragment0090021Acc00300
noncomputable def fragment0090021Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0090021_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 15) (SourceJson.white (fragment0090021Field003Chars00 ++ tail)) fragment0090021Acc00300 =
      SourceJson.object (fuel + 14) (SourceJson.white tail) fragment0090021Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0090021_object_field_003"
  err.flush

noncomputable def fragment0090021Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0090021Field004Value00 : SourceJson := .number (String.ofList ['4'])
noncomputable def fragment0090021Acc00500 : List (String × SourceJson) := (fragment0090021Field004Key00, fragment0090021Field004Value00) :: fragment0090021Acc00400
noncomputable def fragment0090021Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0090021_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 14) (SourceJson.white (fragment0090021Field004Chars00 ++ tail)) fragment0090021Acc00400 =
      .ok (.obj (fragment0090021Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0090021_object_field_004"
  err.flush

noncomputable def fragment0090021Chars : List Char := '{' :: (fragment0090021Field000Chars00 ++ fragment0090021Field001Chars00 ++ fragment0090021Field002Chars00 ++ fragment0090021Field003Chars00 ++ fragment0090021Field004Chars00)
noncomputable def fragment0090021Value : SourceJson := .obj (fragment0090021Acc00500.reverse)

theorem value_fragment0090021 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 19) (fragment0090021Chars ++ tail) =
      .ok (fragment0090021Value, tail) := by
  have hinput : fragment0090021Chars ++ tail = '{' :: (fragment0090021Field000Chars00 ++ (fragment0090021Field001Chars00 ++ (fragment0090021Field002Chars00 ++ (fragment0090021Field003Chars00 ++ (fragment0090021Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0090021Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 19) (fragment0090021Chars ++ tail) =
        SourceJson.value (fuel + 19) ('{' :: (fragment0090021Field000Chars00 ++ (fragment0090021Field001Chars00 ++ (fragment0090021Field002Chars00 ++ (fragment0090021Field003Chars00 ++ (fragment0090021Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 19)) hinput
    _ = SourceJson.object (fuel + 18) (SourceJson.white (fragment0090021Field000Chars00 ++ (fragment0090021Field001Chars00 ++ (fragment0090021Field002Chars00 ++ (fragment0090021Field003Chars00 ++ (fragment0090021Field004Chars00 ++ (tail))))))) fragment0090021Acc00000 := by rfl
    _ = SourceJson.object (fuel + 17) (SourceJson.white (fragment0090021Field001Chars00 ++ (fragment0090021Field002Chars00 ++ (fragment0090021Field003Chars00 ++ (fragment0090021Field004Chars00 ++ (tail)))))) fragment0090021Acc00100 := object_fragment0090021_field_000 fuel (fragment0090021Field001Chars00 ++ (fragment0090021Field002Chars00 ++ (fragment0090021Field003Chars00 ++ (fragment0090021Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 16) (SourceJson.white (fragment0090021Field002Chars00 ++ (fragment0090021Field003Chars00 ++ (fragment0090021Field004Chars00 ++ (tail))))) fragment0090021Acc00200 := object_fragment0090021_field_001 fuel (fragment0090021Field002Chars00 ++ (fragment0090021Field003Chars00 ++ (fragment0090021Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 15) (SourceJson.white (fragment0090021Field003Chars00 ++ (fragment0090021Field004Chars00 ++ (tail)))) fragment0090021Acc00300 := object_fragment0090021_field_002 fuel (fragment0090021Field003Chars00 ++ (fragment0090021Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 14) (SourceJson.white (fragment0090021Field004Chars00 ++ (tail))) fragment0090021Acc00400 := object_fragment0090021_field_003 fuel (fragment0090021Field004Chars00 ++ (tail))
    _ = .ok (fragment0090021Value, tail) := object_fragment0090021_field_004 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0016_before_reader"
  err.flush

noncomputable def chunk0016Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0016Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['6'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['3'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['6'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['4'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['6'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['4']), .number (String.ofList ['6'])], .arr [.number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['6'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['1']))]) :: (acc)

theorem array_chunk0016 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 43) (SourceJson.white (chunk0016Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 42) (SourceJson.white tail) (chunk0016Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0016_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0017_before_reader"
  err.flush

noncomputable def chunk0017Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0017Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['6']), .number (String.ofList ['1', '1'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['4'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['1', '1'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['6'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['1', '1'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['6']), .number (String.ofList ['1', '1'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['4']), .number (String.ofList ['6']), .number (String.ofList ['1', '1'])], .arr [.number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['6']), .number (String.ofList ['1', '1'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['1']))]) :: (acc)

theorem array_chunk0017 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 42) (SourceJson.white (chunk0017Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 41) (SourceJson.white tail) (chunk0017Push00 acc) := by
  rfl

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
noncomputable def chunk0018Chars00 : List Char := chunk0018LeadChars00 ++ fragment0088869Chars ++ chunk0018SuffixChars00
noncomputable def chunk0018Push00 (acc : List SourceJson) : List SourceJson := fragment0088869Value :: acc

noncomputable def chunk0018AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0018_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 41)
      (SourceJson.white (chunk0018LeadChars00 ++ (fragment0088869Chars ++ rest))) acc =
      (SourceJson.value (fuel + 40) (fragment0088869Chars ++ rest)).bind
        (chunk0018AfterValue00 (fuel + 40) acc) := by rfl

theorem array_chunk0018 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 41) (SourceJson.white (chunk0018Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 40) (SourceJson.white tail) (chunk0018Push00 acc) := by
  have hinput : chunk0018Chars00 ++ tail = chunk0018LeadChars00 ++ (fragment0088869Chars ++ (chunk0018SuffixChars00 ++ tail)) := by
    simp only [chunk0018Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 41) (SourceJson.white (chunk0018Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 41)
          (SourceJson.white (chunk0018LeadChars00 ++ (fragment0088869Chars ++ (chunk0018SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 41) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 40) (fragment0088869Chars ++ (chunk0018SuffixChars00 ++ tail))).bind
        (chunk0018AfterValue00 (fuel + 40) acc) := array_chunk0018_head fuel (chunk0018SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0088869Value, chunk0018SuffixChars00 ++ tail)).bind
        (chunk0018AfterValue00 (fuel + 40) acc) :=
      congrArg (fun result => result.bind (chunk0018AfterValue00 (fuel + 40) acc))
        (value_fragment0088869 (fuel + 18) (chunk0018SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 40) (SourceJson.white tail) (chunk0018Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0018_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0019_before_reader"
  err.flush

noncomputable def chunk0019LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0019SuffixChars00 : List Char := [',']
noncomputable def chunk0019Chars00 : List Char := chunk0019LeadChars00 ++ fragment0090021Chars ++ chunk0019SuffixChars00
noncomputable def chunk0019Push00 (acc : List SourceJson) : List SourceJson := fragment0090021Value :: acc

noncomputable def chunk0019AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0019_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 40)
      (SourceJson.white (chunk0019LeadChars00 ++ (fragment0090021Chars ++ rest))) acc =
      (SourceJson.value (fuel + 39) (fragment0090021Chars ++ rest)).bind
        (chunk0019AfterValue00 (fuel + 39) acc) := by rfl

theorem array_chunk0019 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 40) (SourceJson.white (chunk0019Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 39) (SourceJson.white tail) (chunk0019Push00 acc) := by
  have hinput : chunk0019Chars00 ++ tail = chunk0019LeadChars00 ++ (fragment0090021Chars ++ (chunk0019SuffixChars00 ++ tail)) := by
    simp only [chunk0019Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 40) (SourceJson.white (chunk0019Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 40)
          (SourceJson.white (chunk0019LeadChars00 ++ (fragment0090021Chars ++ (chunk0019SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 40) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 39) (fragment0090021Chars ++ (chunk0019SuffixChars00 ++ tail))).bind
        (chunk0019AfterValue00 (fuel + 39) acc) := array_chunk0019_head fuel (chunk0019SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0090021Value, chunk0019SuffixChars00 ++ tail)).bind
        (chunk0019AfterValue00 (fuel + 39) acc) :=
      congrArg (fun result => result.bind (chunk0019AfterValue00 (fuel + 39) acc))
        (value_fragment0090021 (fuel + 20) (chunk0019SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 39) (SourceJson.white tail) (chunk0019Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0019_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0020_before_reader"
  err.flush

noncomputable def chunk0020Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0020Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['0']), .number (String.ofList ['4']), .number (String.ofList ['6'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['2'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['6'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['0']), .number (String.ofList ['4'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['6'])], .arr [.number (String.ofList ['4']), .number (String.ofList ['6'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['1']))]) :: ((.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['0']), .number (String.ofList ['4'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['1'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['4'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['0'])], .arr [.number (String.ofList ['4'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['1']))]) :: (acc))

theorem array_chunk0020 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 39) (SourceJson.white (chunk0020Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 37) (SourceJson.white tail) (chunk0020Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0020_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0021_before_reader"
  err.flush

noncomputable def chunk0021Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '3', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0021Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['0']), .number (String.ofList ['4']), .number (String.ofList ['6']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '8'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['3'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['1', '8'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['0']), .number (String.ofList ['4']), .number (String.ofList ['6'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['4']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '6'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['6']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '8'])], .arr [.number (String.ofList ['4']), .number (String.ofList ['6']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '8'])], .arr [.number (String.ofList ['1', '4']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '8'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['3']))]) :: (acc)

theorem array_chunk0021 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 37) (SourceJson.white (chunk0021Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 36) (SourceJson.white tail) (chunk0021Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0021_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0022_before_reader"
  err.flush

noncomputable def chunk0022Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '2', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0022Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['1']), .number (String.ofList ['3'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['1'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['3'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['1'])], .arr [.number (String.ofList ['3'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['1']))]) :: ((.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['0']), .number (String.ofList ['4']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '6'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['2'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['1', '6'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['0']), .number (String.ofList ['4'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['1', '6'])], .arr [.number (String.ofList ['4']), .number (String.ofList ['1', '4'])], .arr [.number (String.ofList ['1', '4']), .number (String.ofList ['1', '6'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['2']))]) :: (acc))

theorem array_chunk0022 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 36) (SourceJson.white (chunk0022Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 34) (SourceJson.white tail) (chunk0022Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0022_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0023_before_reader"
  err.flush

noncomputable def chunk0023Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0023Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['2'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['5'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['1']), .number (String.ofList ['3'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['5'])], .arr [.number (String.ofList ['3']), .number (String.ofList ['5'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['1']))]) :: (acc)

theorem array_chunk0023 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 34) (SourceJson.white (chunk0023Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 33) (SourceJson.white tail) (chunk0023Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0023_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0016Chars00 ++ chunk0017Chars00 ++ chunk0018Chars00 ++ chunk0019Chars00 ++ chunk0020Chars00 ++ chunk0021Chars00 ++ chunk0022Chars00 ++ chunk0023Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0023Push00 (chunk0022Push00 (chunk0021Push00 (chunk0020Push00 (chunk0019Push00 (chunk0018Push00 (chunk0017Push00 (chunk0016Push00 (acc))))))))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 43) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 33) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0016Chars00 ++ (chunk0017Chars00 ++ (chunk0018Chars00 ++ (chunk0019Chars00 ++ (chunk0020Chars00 ++ (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail)))))))) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 43) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 43) (SourceJson.white (chunk0016Chars00 ++ (chunk0017Chars00 ++ (chunk0018Chars00 ++ (chunk0019Chars00 ++ (chunk0020Chars00 ++ (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail)))))))))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 43) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 42) (SourceJson.white (chunk0017Chars00 ++ (chunk0018Chars00 ++ (chunk0019Chars00 ++ (chunk0020Chars00 ++ (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail))))))))) (chunk0016Push00 (acc)) := array_chunk0016 fuel (chunk0017Chars00 ++ (chunk0018Chars00 ++ (chunk0019Chars00 ++ (chunk0020Chars00 ++ (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail)))))))) (acc)
    _ = SourceJson.array (fuel + 41) (SourceJson.white (chunk0018Chars00 ++ (chunk0019Chars00 ++ (chunk0020Chars00 ++ (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail)))))))) (chunk0017Push00 (chunk0016Push00 (acc))) := array_chunk0017 fuel (chunk0018Chars00 ++ (chunk0019Chars00 ++ (chunk0020Chars00 ++ (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail))))))) (chunk0016Push00 (acc))
    _ = SourceJson.array (fuel + 40) (SourceJson.white (chunk0019Chars00 ++ (chunk0020Chars00 ++ (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail))))))) (chunk0018Push00 (chunk0017Push00 (chunk0016Push00 (acc)))) := array_chunk0018 fuel (chunk0019Chars00 ++ (chunk0020Chars00 ++ (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail)))))) (chunk0017Push00 (chunk0016Push00 (acc)))
    _ = SourceJson.array (fuel + 39) (SourceJson.white (chunk0020Chars00 ++ (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail)))))) (chunk0019Push00 (chunk0018Push00 (chunk0017Push00 (chunk0016Push00 (acc))))) := array_chunk0019 fuel (chunk0020Chars00 ++ (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail))))) (chunk0018Push00 (chunk0017Push00 (chunk0016Push00 (acc))))
    _ = SourceJson.array (fuel + 37) (SourceJson.white (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail))))) (chunk0020Push00 (chunk0019Push00 (chunk0018Push00 (chunk0017Push00 (chunk0016Push00 (acc)))))) := array_chunk0020 fuel (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail)))) (chunk0019Push00 (chunk0018Push00 (chunk0017Push00 (chunk0016Push00 (acc)))))
    _ = SourceJson.array (fuel + 36) (SourceJson.white (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail)))) (chunk0021Push00 (chunk0020Push00 (chunk0019Push00 (chunk0018Push00 (chunk0017Push00 (chunk0016Push00 (acc))))))) := array_chunk0021 fuel (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail))) (chunk0020Push00 (chunk0019Push00 (chunk0018Push00 (chunk0017Push00 (chunk0016Push00 (acc))))))
    _ = SourceJson.array (fuel + 34) (SourceJson.white (chunk0023Chars00 ++ (tail))) (chunk0022Push00 (chunk0021Push00 (chunk0020Push00 (chunk0019Push00 (chunk0018Push00 (chunk0017Push00 (chunk0016Push00 (acc)))))))) := array_chunk0022 fuel (chunk0023Chars00 ++ (tail)) (chunk0021Push00 (chunk0020Push00 (chunk0019Push00 (chunk0018Push00 (chunk0017Push00 (chunk0016Push00 (acc)))))))
    _ = SourceJson.array (fuel + 33) (SourceJson.white tail) (blockPush acc) := array_chunk0023 fuel (tail) (chunk0022Push00 (chunk0021Push00 (chunk0020Push00 (chunk0019Push00 (chunk0018Push00 (chunk0017Push00 (chunk0016Push00 (acc))))))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 87821).take 5144 = blockChars := by rfl

theorem block_original_split : sourceRest 87821 = blockChars ++ sourceRest 92965 := by
  calc
    sourceRest 87821 = (sourceRest 87821).take 5144 ++ (sourceRest 87821).drop 5144 :=
      (List.take_append_drop 5144 (sourceRest 87821)).symm
    _ = blockChars ++ (sourceRest 87821).drop 5144 :=
      congrArg (fun part => part ++ (sourceRest 87821).drop 5144) block_original_prefix
    _ = blockChars ++ sourceRest 92965 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 87821 5144)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 43) (SourceJson.white (sourceRest 87821)) acc =
      SourceJson.array (fuel + 33) (SourceJson.white (sourceRest 92965)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 43) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 92965) acc)

#print axioms array_fragment0089091_chunk_000
#print axioms array_fragment0089091_chunk_001
#print axioms array_fragment0089091_chunk_002
#print axioms array_fragment0089091_chunk_003
#print axioms value_fragment0089091
#print axioms object_fragment0088869_field_000
#print axioms object_fragment0088869_field_001
#print axioms object_fragment0088869_field_002
#print axioms object_fragment0088869_field_003_header
#print axioms object_fragment0088869_field_003
#print axioms object_fragment0088869_field_004
#print axioms value_fragment0088869
#print axioms object_fragment0090021_field_000
#print axioms object_fragment0090021_field_001
#print axioms object_fragment0090021_field_002
#print axioms object_fragment0090021_field_003
#print axioms object_fragment0090021_field_004
#print axioms value_fragment0090021
#print axioms array_chunk0016
#print axioms array_chunk0017
#print axioms array_chunk0018_head
#print axioms array_chunk0018
#print axioms array_chunk0019_head
#print axioms array_chunk0019
#print axioms array_chunk0020
#print axioms array_chunk0021
#print axioms array_chunk0022
#print axioms array_chunk0023
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end FaceLedgerBlock002

end ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
