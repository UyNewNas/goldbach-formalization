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

namespace FaceLedgerBlock004

noncomputable def fragment0100981Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0100981Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0100981Field000Value00 : SourceJson := .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['7']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '1'])]
noncomputable def fragment0100981Acc00100 : List (String × SourceJson) := (fragment0100981Field000Key00, fragment0100981Field000Value00) :: fragment0100981Acc00000
noncomputable def fragment0100981Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0100981_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 18) (SourceJson.white (fragment0100981Field000Chars00 ++ tail)) fragment0100981Acc00000 =
      SourceJson.object (fuel + 17) (SourceJson.white tail) fragment0100981Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0100981_object_field_000"
  err.flush

noncomputable def fragment0100981Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0100981Field001Value00 : SourceJson := .number (String.ofList ['4'])
noncomputable def fragment0100981Acc00200 : List (String × SourceJson) := (fragment0100981Field001Key00, fragment0100981Field001Value00) :: fragment0100981Acc00100
noncomputable def fragment0100981Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '4', ',']

theorem object_fragment0100981_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 17) (SourceJson.white (fragment0100981Field001Chars00 ++ tail)) fragment0100981Acc00100 =
      SourceJson.object (fuel + 16) (SourceJson.white tail) fragment0100981Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0100981_object_field_001"
  err.flush

noncomputable def fragment0100981Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0100981Field002Value00 : SourceJson := .number (String.ofList ['2', '1'])
noncomputable def fragment0100981Acc00300 : List (String × SourceJson) := (fragment0100981Field002Key00, fragment0100981Field002Value00) :: fragment0100981Acc00200
noncomputable def fragment0100981Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '2', '1', ',']

theorem object_fragment0100981_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 16) (SourceJson.white (fragment0100981Field002Chars00 ++ tail)) fragment0100981Acc00200 =
      SourceJson.object (fuel + 15) (SourceJson.white tail) fragment0100981Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0100981_object_field_002"
  err.flush

noncomputable def fragment0100981Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0100981Field003Value00 : SourceJson := .arr [.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['7'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '7']), .number (String.ofList ['2', '1'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['7']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '1'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['5']), .number (String.ofList ['7']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '9'])], .arr [.number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['7']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '1'])], .arr [.number (String.ofList ['1', '5']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '1'])]]
noncomputable def fragment0100981Acc00400 : List (String × SourceJson) := (fragment0100981Field003Key00, fragment0100981Field003Value00) :: fragment0100981Acc00300
noncomputable def fragment0100981Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0100981_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 15) (SourceJson.white (fragment0100981Field003Chars00 ++ tail)) fragment0100981Acc00300 =
      SourceJson.object (fuel + 14) (SourceJson.white tail) fragment0100981Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0100981_object_field_003"
  err.flush

noncomputable def fragment0100981Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0100981Field004Value00 : SourceJson := .number (String.ofList ['4'])
noncomputable def fragment0100981Acc00500 : List (String × SourceJson) := (fragment0100981Field004Key00, fragment0100981Field004Value00) :: fragment0100981Acc00400
noncomputable def fragment0100981Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0100981_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 14) (SourceJson.white (fragment0100981Field004Chars00 ++ tail)) fragment0100981Acc00400 =
      .ok (.obj (fragment0100981Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0100981_object_field_004"
  err.flush

noncomputable def fragment0100981Chars : List Char := '{' :: (fragment0100981Field000Chars00 ++ fragment0100981Field001Chars00 ++ fragment0100981Field002Chars00 ++ fragment0100981Field003Chars00 ++ fragment0100981Field004Chars00)
noncomputable def fragment0100981Value : SourceJson := .obj (fragment0100981Acc00500.reverse)

theorem value_fragment0100981 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 19) (fragment0100981Chars ++ tail) =
      .ok (fragment0100981Value, tail) := by
  have hinput : fragment0100981Chars ++ tail = '{' :: (fragment0100981Field000Chars00 ++ (fragment0100981Field001Chars00 ++ (fragment0100981Field002Chars00 ++ (fragment0100981Field003Chars00 ++ (fragment0100981Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0100981Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 19) (fragment0100981Chars ++ tail) =
        SourceJson.value (fuel + 19) ('{' :: (fragment0100981Field000Chars00 ++ (fragment0100981Field001Chars00 ++ (fragment0100981Field002Chars00 ++ (fragment0100981Field003Chars00 ++ (fragment0100981Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 19)) hinput
    _ = SourceJson.object (fuel + 18) (SourceJson.white (fragment0100981Field000Chars00 ++ (fragment0100981Field001Chars00 ++ (fragment0100981Field002Chars00 ++ (fragment0100981Field003Chars00 ++ (fragment0100981Field004Chars00 ++ (tail))))))) fragment0100981Acc00000 := by rfl
    _ = SourceJson.object (fuel + 17) (SourceJson.white (fragment0100981Field001Chars00 ++ (fragment0100981Field002Chars00 ++ (fragment0100981Field003Chars00 ++ (fragment0100981Field004Chars00 ++ (tail)))))) fragment0100981Acc00100 := object_fragment0100981_field_000 fuel (fragment0100981Field001Chars00 ++ (fragment0100981Field002Chars00 ++ (fragment0100981Field003Chars00 ++ (fragment0100981Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 16) (SourceJson.white (fragment0100981Field002Chars00 ++ (fragment0100981Field003Chars00 ++ (fragment0100981Field004Chars00 ++ (tail))))) fragment0100981Acc00200 := object_fragment0100981_field_001 fuel (fragment0100981Field002Chars00 ++ (fragment0100981Field003Chars00 ++ (fragment0100981Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 15) (SourceJson.white (fragment0100981Field003Chars00 ++ (fragment0100981Field004Chars00 ++ (tail)))) fragment0100981Acc00300 := object_fragment0100981_field_002 fuel (fragment0100981Field003Chars00 ++ (fragment0100981Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 14) (SourceJson.white (fragment0100981Field004Chars00 ++ (tail))) fragment0100981Acc00400 := object_fragment0100981_field_003 fuel (fragment0100981Field004Chars00 ++ (tail))
    _ = .ok (fragment0100981Value, tail) := object_fragment0100981_field_004 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0032_before_reader"
  err.flush

noncomputable def chunk0032LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0032SuffixChars00 : List Char := [',']
noncomputable def chunk0032Chars00 : List Char := chunk0032LeadChars00 ++ fragment0100981Chars ++ chunk0032SuffixChars00
noncomputable def chunk0032Push00 (acc : List SourceJson) : List SourceJson := fragment0100981Value :: acc

noncomputable def chunk0032AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0032_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 25)
      (SourceJson.white (chunk0032LeadChars00 ++ (fragment0100981Chars ++ rest))) acc =
      (SourceJson.value (fuel + 24) (fragment0100981Chars ++ rest)).bind
        (chunk0032AfterValue00 (fuel + 24) acc) := by rfl

theorem array_chunk0032 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 25) (SourceJson.white (chunk0032Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 24) (SourceJson.white tail) (chunk0032Push00 acc) := by
  have hinput : chunk0032Chars00 ++ tail = chunk0032LeadChars00 ++ (fragment0100981Chars ++ (chunk0032SuffixChars00 ++ tail)) := by
    simp only [chunk0032Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 25) (SourceJson.white (chunk0032Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 25)
          (SourceJson.white (chunk0032LeadChars00 ++ (fragment0100981Chars ++ (chunk0032SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 25) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 24) (fragment0100981Chars ++ (chunk0032SuffixChars00 ++ tail))).bind
        (chunk0032AfterValue00 (fuel + 24) acc) := array_chunk0032_head fuel (chunk0032SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0100981Value, chunk0032SuffixChars00 ++ tail)).bind
        (chunk0032AfterValue00 (fuel + 24) acc) :=
      congrArg (fun result => result.bind (chunk0032AfterValue00 (fuel + 24) acc))
        (value_fragment0100981 (fuel + 5) (chunk0032SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 24) (SourceJson.white tail) (chunk0032Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0032_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0033_before_reader"
  err.flush

noncomputable def chunk0033Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0033Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['1']), .number (String.ofList ['5']), .number (String.ofList ['7'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['2'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['7'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['1']), .number (String.ofList ['5'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['7'])], .arr [.number (String.ofList ['5']), .number (String.ofList ['7'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['1']))]) :: ((.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['1']), .number (String.ofList ['5'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['1'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['5'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['1'])], .arr [.number (String.ofList ['5'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['1']))]) :: (acc))

theorem array_chunk0033 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 24) (SourceJson.white (chunk0033Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 22) (SourceJson.white tail) (chunk0033Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0033_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0034_before_reader"
  err.flush

noncomputable def chunk0034Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '3', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0034Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['1']), .number (String.ofList ['5']), .number (String.ofList ['7']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '9'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['3'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['1', '9'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['1']), .number (String.ofList ['5']), .number (String.ofList ['7'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['5']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '7'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['7']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '9'])], .arr [.number (String.ofList ['5']), .number (String.ofList ['7']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '9'])], .arr [.number (String.ofList ['1', '5']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '9'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['3']))]) :: (acc)

theorem array_chunk0034 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 22) (SourceJson.white (chunk0034Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 21) (SourceJson.white tail) (chunk0034Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0034_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0035_before_reader"
  err.flush

noncomputable def chunk0035Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '2', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0035Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['4']), .number (String.ofList ['5'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['1'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['5'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['4'])], .arr [.number (String.ofList ['5'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['1']))]) :: ((.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['1']), .number (String.ofList ['5']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '7'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['2'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['1', '7'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['1']), .number (String.ofList ['5'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['1', '7'])], .arr [.number (String.ofList ['5']), .number (String.ofList ['1', '5'])], .arr [.number (String.ofList ['1', '5']), .number (String.ofList ['1', '7'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['2']))]) :: (acc))

theorem array_chunk0035 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 21) (SourceJson.white (chunk0035Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 19) (SourceJson.white tail) (chunk0035Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0035_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0036_before_reader"
  err.flush

noncomputable def chunk0036Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '2', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0036Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['4']), .number (String.ofList ['1', '4'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['1'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['1', '4'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['4'])], .arr [.number (String.ofList ['1', '4'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['1']))]) :: ((.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['2'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['1', '5'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['4']), .number (String.ofList ['5'])], .arr [.number (String.ofList ['4']), .number (String.ofList ['1', '4'])], .arr [.number (String.ofList ['5']), .number (String.ofList ['1', '5'])], .arr [.number (String.ofList ['1', '4']), .number (String.ofList ['1', '5'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['2']))]) :: (acc))

theorem array_chunk0036 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 19) (SourceJson.white (chunk0036Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 17) (SourceJson.white tail) (chunk0036Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0036_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0037_before_reader"
  err.flush

noncomputable def chunk0037Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}', '\r', '\n', ' ', ' ', ']']
noncomputable def chunk0037Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['5']), .number (String.ofList ['1', '5'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['1'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['1', '5'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['5'])], .arr [.number (String.ofList ['1', '5'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['1']))]) :: (acc)

theorem array_chunk0037 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 17) (SourceJson.white (chunk0037Chars00 ++ tail)) acc =
      .ok (.arr ((chunk0037Push00 acc).reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0037_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0032Chars00 ++ chunk0033Chars00 ++ chunk0034Chars00 ++ chunk0035Chars00 ++ chunk0036Chars00 ++ chunk0037Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0037Push00 (chunk0036Push00 (chunk0035Push00 (chunk0034Push00 (chunk0033Push00 (chunk0032Push00 (acc))))))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 25) (SourceJson.white (blockChars ++ tail)) acc =
      .ok (.arr ((blockPush acc).reverse), tail) := by
  have hinput : blockChars ++ tail = chunk0032Chars00 ++ (chunk0033Chars00 ++ (chunk0034Chars00 ++ (chunk0035Chars00 ++ (chunk0036Chars00 ++ (chunk0037Chars00 ++ (tail)))))) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 25) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 25) (SourceJson.white (chunk0032Chars00 ++ (chunk0033Chars00 ++ (chunk0034Chars00 ++ (chunk0035Chars00 ++ (chunk0036Chars00 ++ (chunk0037Chars00 ++ (tail)))))))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 25) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 24) (SourceJson.white (chunk0033Chars00 ++ (chunk0034Chars00 ++ (chunk0035Chars00 ++ (chunk0036Chars00 ++ (chunk0037Chars00 ++ (tail))))))) (chunk0032Push00 (acc)) := array_chunk0032 fuel (chunk0033Chars00 ++ (chunk0034Chars00 ++ (chunk0035Chars00 ++ (chunk0036Chars00 ++ (chunk0037Chars00 ++ (tail)))))) (acc)
    _ = SourceJson.array (fuel + 22) (SourceJson.white (chunk0034Chars00 ++ (chunk0035Chars00 ++ (chunk0036Chars00 ++ (chunk0037Chars00 ++ (tail)))))) (chunk0033Push00 (chunk0032Push00 (acc))) := array_chunk0033 fuel (chunk0034Chars00 ++ (chunk0035Chars00 ++ (chunk0036Chars00 ++ (chunk0037Chars00 ++ (tail))))) (chunk0032Push00 (acc))
    _ = SourceJson.array (fuel + 21) (SourceJson.white (chunk0035Chars00 ++ (chunk0036Chars00 ++ (chunk0037Chars00 ++ (tail))))) (chunk0034Push00 (chunk0033Push00 (chunk0032Push00 (acc)))) := array_chunk0034 fuel (chunk0035Chars00 ++ (chunk0036Chars00 ++ (chunk0037Chars00 ++ (tail)))) (chunk0033Push00 (chunk0032Push00 (acc)))
    _ = SourceJson.array (fuel + 19) (SourceJson.white (chunk0036Chars00 ++ (chunk0037Chars00 ++ (tail)))) (chunk0035Push00 (chunk0034Push00 (chunk0033Push00 (chunk0032Push00 (acc))))) := array_chunk0035 fuel (chunk0036Chars00 ++ (chunk0037Chars00 ++ (tail))) (chunk0034Push00 (chunk0033Push00 (chunk0032Push00 (acc))))
    _ = SourceJson.array (fuel + 17) (SourceJson.white (chunk0037Chars00 ++ (tail))) (chunk0036Push00 (chunk0035Push00 (chunk0034Push00 (chunk0033Push00 (chunk0032Push00 (acc)))))) := array_chunk0036 fuel (chunk0037Chars00 ++ (tail)) (chunk0035Push00 (chunk0034Push00 (chunk0033Push00 (chunk0032Push00 (acc)))))
    _ = .ok (.arr ((blockPush acc).reverse), tail) := array_chunk0037 fuel (tail) (chunk0036Push00 (chunk0035Push00 (chunk0034Push00 (chunk0033Push00 (chunk0032Push00 (acc))))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 100975).take 3503 = blockChars := by rfl

theorem block_original_split : sourceRest 100975 = blockChars ++ sourceRest 104478 := by
  calc
    sourceRest 100975 = (sourceRest 100975).take 3503 ++ (sourceRest 100975).drop 3503 :=
      (List.take_append_drop 3503 (sourceRest 100975)).symm
    _ = blockChars ++ (sourceRest 100975).drop 3503 :=
      congrArg (fun part => part ++ (sourceRest 100975).drop 3503) block_original_prefix
    _ = blockChars ++ sourceRest 104478 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 100975 3503)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 25) (SourceJson.white (sourceRest 100975)) acc =
      .ok (.arr ((blockPush acc).reverse), sourceRest 104478) :=
  (congrArg (fun chars => SourceJson.array (fuel + 25) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 104478) acc)

#print axioms object_fragment0100981_field_000
#print axioms object_fragment0100981_field_001
#print axioms object_fragment0100981_field_002
#print axioms object_fragment0100981_field_003
#print axioms object_fragment0100981_field_004
#print axioms value_fragment0100981
#print axioms array_chunk0032_head
#print axioms array_chunk0032
#print axioms array_chunk0033
#print axioms array_chunk0034
#print axioms array_chunk0035
#print axioms array_chunk0036
#print axioms array_chunk0037
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end FaceLedgerBlock004

end ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
