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

namespace FaceLedgerBlock006

noncomputable def fragment0120838Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0120838Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0120838Field000Value00 : SourceJson := .arr [.number (String.ofList ['7']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7'])]
noncomputable def fragment0120838Acc00100 : List (String × SourceJson) := (fragment0120838Field000Key00, fragment0120838Field000Value00) :: fragment0120838Acc00000
noncomputable def fragment0120838Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0120838_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 18) (SourceJson.white (fragment0120838Field000Chars00 ++ tail)) fragment0120838Acc00000 =
      SourceJson.object (fuel + 17) (SourceJson.white tail) fragment0120838Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0120838_object_field_000"
  err.flush

noncomputable def fragment0120838Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0120838Field001Value00 : SourceJson := .number (String.ofList ['5'])
noncomputable def fragment0120838Acc00200 : List (String × SourceJson) := (fragment0120838Field001Key00, fragment0120838Field001Value00) :: fragment0120838Acc00100
noncomputable def fragment0120838Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '5', ',']

theorem object_fragment0120838_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 17) (SourceJson.white (fragment0120838Field001Chars00 ++ tail)) fragment0120838Acc00100 =
      SourceJson.object (fuel + 16) (SourceJson.white tail) fragment0120838Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0120838_object_field_001"
  err.flush

noncomputable def fragment0120838Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0120838Field002Value00 : SourceJson := .number (String.ofList ['1', '7'])
noncomputable def fragment0120838Acc00300 : List (String × SourceJson) := (fragment0120838Field002Key00, fragment0120838Field002Value00) :: fragment0120838Acc00200
noncomputable def fragment0120838Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '1', '7', ',']

theorem object_fragment0120838_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 16) (SourceJson.white (fragment0120838Field002Chars00 ++ tail)) fragment0120838Acc00200 =
      SourceJson.object (fuel + 15) (SourceJson.white tail) fragment0120838Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0120838_object_field_002"
  err.flush

noncomputable def fragment0120838Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0120838Field003Value00 : SourceJson := .arr [.arr [.number (String.ofList ['7']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '6'])], .arr [.number (String.ofList ['7']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '7'])], .arr [.number (String.ofList ['7']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7'])], .arr [.number (String.ofList ['7']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7'])], .arr [.number (String.ofList ['7']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7'])], .arr [.number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7'])]]
noncomputable def fragment0120838Acc00400 : List (String × SourceJson) := (fragment0120838Field003Key00, fragment0120838Field003Value00) :: fragment0120838Acc00300
noncomputable def fragment0120838Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0120838_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 15) (SourceJson.white (fragment0120838Field003Chars00 ++ tail)) fragment0120838Acc00300 =
      SourceJson.object (fuel + 14) (SourceJson.white tail) fragment0120838Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0120838_object_field_003"
  err.flush

noncomputable def fragment0120838Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0120838Field004Value00 : SourceJson := .number (String.ofList ['1'])
noncomputable def fragment0120838Acc00500 : List (String × SourceJson) := (fragment0120838Field004Key00, fragment0120838Field004Value00) :: fragment0120838Acc00400
noncomputable def fragment0120838Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0120838_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 14) (SourceJson.white (fragment0120838Field004Chars00 ++ tail)) fragment0120838Acc00400 =
      .ok (.obj (fragment0120838Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0120838_object_field_004"
  err.flush

noncomputable def fragment0120838Chars : List Char := '{' :: (fragment0120838Field000Chars00 ++ fragment0120838Field001Chars00 ++ fragment0120838Field002Chars00 ++ fragment0120838Field003Chars00 ++ fragment0120838Field004Chars00)
noncomputable def fragment0120838Value : SourceJson := .obj (fragment0120838Acc00500.reverse)

theorem value_fragment0120838 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 19) (fragment0120838Chars ++ tail) =
      .ok (fragment0120838Value, tail) := by
  have hinput : fragment0120838Chars ++ tail = '{' :: (fragment0120838Field000Chars00 ++ (fragment0120838Field001Chars00 ++ (fragment0120838Field002Chars00 ++ (fragment0120838Field003Chars00 ++ (fragment0120838Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0120838Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 19) (fragment0120838Chars ++ tail) =
        SourceJson.value (fuel + 19) ('{' :: (fragment0120838Field000Chars00 ++ (fragment0120838Field001Chars00 ++ (fragment0120838Field002Chars00 ++ (fragment0120838Field003Chars00 ++ (fragment0120838Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 19)) hinput
    _ = SourceJson.object (fuel + 18) (SourceJson.white (fragment0120838Field000Chars00 ++ (fragment0120838Field001Chars00 ++ (fragment0120838Field002Chars00 ++ (fragment0120838Field003Chars00 ++ (fragment0120838Field004Chars00 ++ (tail))))))) fragment0120838Acc00000 := by rfl
    _ = SourceJson.object (fuel + 17) (SourceJson.white (fragment0120838Field001Chars00 ++ (fragment0120838Field002Chars00 ++ (fragment0120838Field003Chars00 ++ (fragment0120838Field004Chars00 ++ (tail)))))) fragment0120838Acc00100 := object_fragment0120838_field_000 fuel (fragment0120838Field001Chars00 ++ (fragment0120838Field002Chars00 ++ (fragment0120838Field003Chars00 ++ (fragment0120838Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 16) (SourceJson.white (fragment0120838Field002Chars00 ++ (fragment0120838Field003Chars00 ++ (fragment0120838Field004Chars00 ++ (tail))))) fragment0120838Acc00200 := object_fragment0120838_field_001 fuel (fragment0120838Field002Chars00 ++ (fragment0120838Field003Chars00 ++ (fragment0120838Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 15) (SourceJson.white (fragment0120838Field003Chars00 ++ (fragment0120838Field004Chars00 ++ (tail)))) fragment0120838Acc00300 := object_fragment0120838_field_002 fuel (fragment0120838Field003Chars00 ++ (fragment0120838Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 14) (SourceJson.white (fragment0120838Field004Chars00 ++ (tail))) fragment0120838Acc00400 := object_fragment0120838_field_003 fuel (fragment0120838Field004Chars00 ++ (tail))
    _ = .ok (fragment0120838Value, tail) := object_fragment0120838_field_004 fuel (tail)

noncomputable def fragment0121820Acc00000 : List SourceJson := []

noncomputable def fragment0121820Chunk000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0121820Chunk000Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['7']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '9'])]) :: ((.arr [.number (String.ofList ['7']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7'])]) :: (acc))

theorem array_fragment0121820_chunk_000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 15) (SourceJson.white (fragment0121820Chunk000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 13) (SourceJson.white tail) (fragment0121820Chunk000Push00 acc) := by
  rfl

noncomputable def fragment0121820Acc00100 : List SourceJson := fragment0121820Chunk000Push00 fragment0121820Acc00000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0121820_array_chunk_000"
  err.flush

noncomputable def fragment0121820Chunk001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0121820Chunk001Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['7']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '9'])]) :: ((.arr [.number (String.ofList ['7']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '9'])]) :: (acc))

theorem array_fragment0121820_chunk_001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 13) (SourceJson.white (fragment0121820Chunk001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 11) (SourceJson.white tail) (fragment0121820Chunk001Push00 acc) := by
  rfl

noncomputable def fragment0121820Acc00200 : List SourceJson := fragment0121820Chunk001Push00 fragment0121820Acc00100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0121820_array_chunk_001"
  err.flush

noncomputable def fragment0121820Chunk002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0121820Chunk002Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['7']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '9'])]) :: ((.arr [.number (String.ofList ['7']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '9'])]) :: (acc))

theorem array_fragment0121820_chunk_002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 11) (SourceJson.white (fragment0121820Chunk002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 9) (SourceJson.white tail) (fragment0121820Chunk002Push00 acc) := by
  rfl

noncomputable def fragment0121820Acc00300 : List SourceJson := fragment0121820Chunk002Push00 fragment0121820Acc00200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0121820_array_chunk_002"
  err.flush

noncomputable def fragment0121820Chunk003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']']
noncomputable def fragment0121820Chunk003Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '9'])]) :: (acc)

theorem array_fragment0121820_chunk_003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 9) (SourceJson.white (fragment0121820Chunk003Chars00 ++ tail)) acc =
      .ok (.arr ((fragment0121820Chunk003Push00 acc).reverse), tail) := by
  rfl

noncomputable def fragment0121820Acc00400 : List SourceJson := fragment0121820Chunk003Push00 fragment0121820Acc00300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0121820_array_chunk_003"
  err.flush

noncomputable def fragment0121820Chars : List Char := '[' :: (fragment0121820Chunk000Chars00 ++ fragment0121820Chunk001Chars00 ++ fragment0121820Chunk002Chars00 ++ fragment0121820Chunk003Chars00)
noncomputable def fragment0121820Value : SourceJson := .arr (fragment0121820Acc00400.reverse)

theorem value_fragment0121820 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 16) (fragment0121820Chars ++ tail) =
      .ok (fragment0121820Value, tail) := by
  have hinput : fragment0121820Chars ++ tail = '[' :: (fragment0121820Chunk000Chars00 ++ (fragment0121820Chunk001Chars00 ++ (fragment0121820Chunk002Chars00 ++ (fragment0121820Chunk003Chars00 ++ (tail))))) := by
    simp only [fragment0121820Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 16) (fragment0121820Chars ++ tail) =
        SourceJson.value (fuel + 16) ('[' :: (fragment0121820Chunk000Chars00 ++ (fragment0121820Chunk001Chars00 ++ (fragment0121820Chunk002Chars00 ++ (fragment0121820Chunk003Chars00 ++ (tail)))))) :=
      congrArg (SourceJson.value (fuel + 16)) hinput
    _ = SourceJson.array (fuel + 15) (SourceJson.white (fragment0121820Chunk000Chars00 ++ (fragment0121820Chunk001Chars00 ++ (fragment0121820Chunk002Chars00 ++ (fragment0121820Chunk003Chars00 ++ (tail)))))) fragment0121820Acc00000 := by rfl
    _ = SourceJson.array (fuel + 13) (SourceJson.white (fragment0121820Chunk001Chars00 ++ (fragment0121820Chunk002Chars00 ++ (fragment0121820Chunk003Chars00 ++ (tail))))) fragment0121820Acc00100 := array_fragment0121820_chunk_000 fuel (fragment0121820Chunk001Chars00 ++ (fragment0121820Chunk002Chars00 ++ (fragment0121820Chunk003Chars00 ++ (tail)))) fragment0121820Acc00000
    _ = SourceJson.array (fuel + 11) (SourceJson.white (fragment0121820Chunk002Chars00 ++ (fragment0121820Chunk003Chars00 ++ (tail)))) fragment0121820Acc00200 := array_fragment0121820_chunk_001 fuel (fragment0121820Chunk002Chars00 ++ (fragment0121820Chunk003Chars00 ++ (tail))) fragment0121820Acc00100
    _ = SourceJson.array (fuel + 9) (SourceJson.white (fragment0121820Chunk003Chars00 ++ (tail))) fragment0121820Acc00300 := array_fragment0121820_chunk_002 fuel (fragment0121820Chunk003Chars00 ++ (tail)) fragment0121820Acc00200
    _ = .ok (fragment0121820Value, tail) := array_fragment0121820_chunk_003 fuel (tail) fragment0121820Acc00300

noncomputable def fragment0121634Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0121634Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0121634Field000Value00 : SourceJson := .arr [.number (String.ofList ['7']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '9'])]
noncomputable def fragment0121634Acc00100 : List (String × SourceJson) := (fragment0121634Field000Key00, fragment0121634Field000Value00) :: fragment0121634Acc00000
noncomputable def fragment0121634Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0121634_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 20) (SourceJson.white (fragment0121634Field000Chars00 ++ tail)) fragment0121634Acc00000 =
      SourceJson.object (fuel + 19) (SourceJson.white tail) fragment0121634Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0121634_object_field_000"
  err.flush

noncomputable def fragment0121634Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0121634Field001Value00 : SourceJson := .number (String.ofList ['6'])
noncomputable def fragment0121634Acc00200 : List (String × SourceJson) := (fragment0121634Field001Key00, fragment0121634Field001Value00) :: fragment0121634Acc00100
noncomputable def fragment0121634Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '6', ',']

theorem object_fragment0121634_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 19) (SourceJson.white (fragment0121634Field001Chars00 ++ tail)) fragment0121634Acc00100 =
      SourceJson.object (fuel + 18) (SourceJson.white tail) fragment0121634Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0121634_object_field_001"
  err.flush

noncomputable def fragment0121634Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0121634Field002Value00 : SourceJson := .number (String.ofList ['1', '9'])
noncomputable def fragment0121634Acc00300 : List (String × SourceJson) := (fragment0121634Field002Key00, fragment0121634Field002Value00) :: fragment0121634Acc00200
noncomputable def fragment0121634Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '1', '9', ',']

theorem object_fragment0121634_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 18) (SourceJson.white (fragment0121634Field002Chars00 ++ tail)) fragment0121634Acc00200 =
      SourceJson.object (fuel + 17) (SourceJson.white tail) fragment0121634Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0121634_object_field_002"
  err.flush

noncomputable def fragment0121634Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0121634Field003Value00 : SourceJson := fragment0121820Value
noncomputable def fragment0121634Acc00400 : List (String × SourceJson) := (fragment0121634Field003Key00, fragment0121634Field003Value00) :: fragment0121634Acc00300
noncomputable def fragment0121634Field003HeaderChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ']
noncomputable def fragment0121634Field003SuffixChars00 : List Char := [',']
noncomputable def fragment0121634Field003Chars00 : List Char := fragment0121634Field003HeaderChars00 ++ fragment0121820Chars ++ fragment0121634Field003SuffixChars00

noncomputable def fragment0121634Field003AfterValue00 (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending => .ok (.obj (((fragment0121634Field003Key00, result.1) :: fragment0121634Acc00300).reverse), ending)
  | ',' :: ending => SourceJson.object fuel (SourceJson.white ending) ((fragment0121634Field003Key00, result.1) :: fragment0121634Acc00300)
  | _ => .error "object separator missing"

theorem object_fragment0121634_field_003_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 17) (SourceJson.white (fragment0121634Field003HeaderChars00 ++ rest)) fragment0121634Acc00300 =
      (SourceJson.value (fuel + 16) rest).bind (fragment0121634Field003AfterValue00 (fuel + 16)) := by rfl

theorem object_fragment0121634_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 17) (SourceJson.white (fragment0121634Field003Chars00 ++ tail)) fragment0121634Acc00300 =
      SourceJson.object (fuel + 16) (SourceJson.white tail) fragment0121634Acc00400 := by
  have hinput : fragment0121634Field003Chars00 ++ tail = fragment0121634Field003HeaderChars00 ++ (fragment0121820Chars ++ (fragment0121634Field003SuffixChars00 ++ tail)) := by
    simp only [fragment0121634Field003Chars00, List.append_assoc]
  calc
    SourceJson.object (fuel + 17) (SourceJson.white (fragment0121634Field003Chars00 ++ tail)) fragment0121634Acc00300 =
        SourceJson.object (fuel + 17)
          (SourceJson.white (fragment0121634Field003HeaderChars00 ++ (fragment0121820Chars ++ (fragment0121634Field003SuffixChars00 ++ tail)))) fragment0121634Acc00300 :=
      congrArg (fun s => SourceJson.object (fuel + 17) (SourceJson.white s) fragment0121634Acc00300) hinput
    _ = (SourceJson.value (fuel + 16) (fragment0121820Chars ++ (fragment0121634Field003SuffixChars00 ++ tail))).bind
        (fragment0121634Field003AfterValue00 (fuel + 16)) := object_fragment0121634_field_003_header fuel (fragment0121820Chars ++ (fragment0121634Field003SuffixChars00 ++ tail))
    _ = (Except.ok (fragment0121820Value, fragment0121634Field003SuffixChars00 ++ tail)).bind (fragment0121634Field003AfterValue00 (fuel + 16)) :=
      congrArg (fun result => result.bind (fragment0121634Field003AfterValue00 (fuel + 16)))
        (value_fragment0121820 (fuel + 0) (fragment0121634Field003SuffixChars00 ++ tail))
    _ = SourceJson.object (fuel + 16) (SourceJson.white tail) fragment0121634Acc00400 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0121634_object_field_003"
  err.flush

noncomputable def fragment0121634Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0121634Field004Value00 : SourceJson := .number (String.ofList ['1'])
noncomputable def fragment0121634Acc00500 : List (String × SourceJson) := (fragment0121634Field004Key00, fragment0121634Field004Value00) :: fragment0121634Acc00400
noncomputable def fragment0121634Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0121634_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 16) (SourceJson.white (fragment0121634Field004Chars00 ++ tail)) fragment0121634Acc00400 =
      .ok (.obj (fragment0121634Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0121634_object_field_004"
  err.flush

noncomputable def fragment0121634Chars : List Char := '{' :: (fragment0121634Field000Chars00 ++ fragment0121634Field001Chars00 ++ fragment0121634Field002Chars00 ++ fragment0121634Field003Chars00 ++ fragment0121634Field004Chars00)
noncomputable def fragment0121634Value : SourceJson := .obj (fragment0121634Acc00500.reverse)

theorem value_fragment0121634 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 21) (fragment0121634Chars ++ tail) =
      .ok (fragment0121634Value, tail) := by
  have hinput : fragment0121634Chars ++ tail = '{' :: (fragment0121634Field000Chars00 ++ (fragment0121634Field001Chars00 ++ (fragment0121634Field002Chars00 ++ (fragment0121634Field003Chars00 ++ (fragment0121634Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0121634Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 21) (fragment0121634Chars ++ tail) =
        SourceJson.value (fuel + 21) ('{' :: (fragment0121634Field000Chars00 ++ (fragment0121634Field001Chars00 ++ (fragment0121634Field002Chars00 ++ (fragment0121634Field003Chars00 ++ (fragment0121634Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 21)) hinput
    _ = SourceJson.object (fuel + 20) (SourceJson.white (fragment0121634Field000Chars00 ++ (fragment0121634Field001Chars00 ++ (fragment0121634Field002Chars00 ++ (fragment0121634Field003Chars00 ++ (fragment0121634Field004Chars00 ++ (tail))))))) fragment0121634Acc00000 := by rfl
    _ = SourceJson.object (fuel + 19) (SourceJson.white (fragment0121634Field001Chars00 ++ (fragment0121634Field002Chars00 ++ (fragment0121634Field003Chars00 ++ (fragment0121634Field004Chars00 ++ (tail)))))) fragment0121634Acc00100 := object_fragment0121634_field_000 fuel (fragment0121634Field001Chars00 ++ (fragment0121634Field002Chars00 ++ (fragment0121634Field003Chars00 ++ (fragment0121634Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 18) (SourceJson.white (fragment0121634Field002Chars00 ++ (fragment0121634Field003Chars00 ++ (fragment0121634Field004Chars00 ++ (tail))))) fragment0121634Acc00200 := object_fragment0121634_field_001 fuel (fragment0121634Field002Chars00 ++ (fragment0121634Field003Chars00 ++ (fragment0121634Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 17) (SourceJson.white (fragment0121634Field003Chars00 ++ (fragment0121634Field004Chars00 ++ (tail)))) fragment0121634Acc00300 := object_fragment0121634_field_002 fuel (fragment0121634Field003Chars00 ++ (fragment0121634Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 16) (SourceJson.white (fragment0121634Field004Chars00 ++ (tail))) fragment0121634Acc00400 := object_fragment0121634_field_003 fuel (fragment0121634Field004Chars00 ++ (tail))
    _ = .ok (fragment0121634Value, tail) := object_fragment0121634_field_004 fuel (tail)

noncomputable def fragment0122644Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0122644Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0122644Field000Value00 : SourceJson := .arr [.number (String.ofList ['7']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '9'])]
noncomputable def fragment0122644Acc00100 : List (String × SourceJson) := (fragment0122644Field000Key00, fragment0122644Field000Value00) :: fragment0122644Acc00000
noncomputable def fragment0122644Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0122644_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 18) (SourceJson.white (fragment0122644Field000Chars00 ++ tail)) fragment0122644Acc00000 =
      SourceJson.object (fuel + 17) (SourceJson.white tail) fragment0122644Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0122644_object_field_000"
  err.flush

noncomputable def fragment0122644Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0122644Field001Value00 : SourceJson := .number (String.ofList ['5'])
noncomputable def fragment0122644Acc00200 : List (String × SourceJson) := (fragment0122644Field001Key00, fragment0122644Field001Value00) :: fragment0122644Acc00100
noncomputable def fragment0122644Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '5', ',']

theorem object_fragment0122644_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 17) (SourceJson.white (fragment0122644Field001Chars00 ++ tail)) fragment0122644Acc00100 =
      SourceJson.object (fuel + 16) (SourceJson.white tail) fragment0122644Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0122644_object_field_001"
  err.flush

noncomputable def fragment0122644Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0122644Field002Value00 : SourceJson := .number (String.ofList ['1', '9'])
noncomputable def fragment0122644Acc00300 : List (String × SourceJson) := (fragment0122644Field002Key00, fragment0122644Field002Value00) :: fragment0122644Acc00200
noncomputable def fragment0122644Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '1', '9', ',']

theorem object_fragment0122644_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 16) (SourceJson.white (fragment0122644Field002Chars00 ++ tail)) fragment0122644Acc00200 =
      SourceJson.object (fuel + 15) (SourceJson.white tail) fragment0122644Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0122644_object_field_002"
  err.flush

noncomputable def fragment0122644Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0122644Field003Value00 : SourceJson := .arr [.arr [.number (String.ofList ['7']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '6'])], .arr [.number (String.ofList ['7']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '9'])], .arr [.number (String.ofList ['7']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '9'])], .arr [.number (String.ofList ['7']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '9'])], .arr [.number (String.ofList ['7']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '9'])], .arr [.number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '9'])]]
noncomputable def fragment0122644Acc00400 : List (String × SourceJson) := (fragment0122644Field003Key00, fragment0122644Field003Value00) :: fragment0122644Acc00300
noncomputable def fragment0122644Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0122644_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 15) (SourceJson.white (fragment0122644Field003Chars00 ++ tail)) fragment0122644Acc00300 =
      SourceJson.object (fuel + 14) (SourceJson.white tail) fragment0122644Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0122644_object_field_003"
  err.flush

noncomputable def fragment0122644Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0122644Field004Value00 : SourceJson := .number (String.ofList ['1'])
noncomputable def fragment0122644Acc00500 : List (String × SourceJson) := (fragment0122644Field004Key00, fragment0122644Field004Value00) :: fragment0122644Acc00400
noncomputable def fragment0122644Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0122644_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 14) (SourceJson.white (fragment0122644Field004Chars00 ++ tail)) fragment0122644Acc00400 =
      .ok (.obj (fragment0122644Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0122644_object_field_004"
  err.flush

noncomputable def fragment0122644Chars : List Char := '{' :: (fragment0122644Field000Chars00 ++ fragment0122644Field001Chars00 ++ fragment0122644Field002Chars00 ++ fragment0122644Field003Chars00 ++ fragment0122644Field004Chars00)
noncomputable def fragment0122644Value : SourceJson := .obj (fragment0122644Acc00500.reverse)

theorem value_fragment0122644 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 19) (fragment0122644Chars ++ tail) =
      .ok (fragment0122644Value, tail) := by
  have hinput : fragment0122644Chars ++ tail = '{' :: (fragment0122644Field000Chars00 ++ (fragment0122644Field001Chars00 ++ (fragment0122644Field002Chars00 ++ (fragment0122644Field003Chars00 ++ (fragment0122644Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0122644Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 19) (fragment0122644Chars ++ tail) =
        SourceJson.value (fuel + 19) ('{' :: (fragment0122644Field000Chars00 ++ (fragment0122644Field001Chars00 ++ (fragment0122644Field002Chars00 ++ (fragment0122644Field003Chars00 ++ (fragment0122644Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 19)) hinput
    _ = SourceJson.object (fuel + 18) (SourceJson.white (fragment0122644Field000Chars00 ++ (fragment0122644Field001Chars00 ++ (fragment0122644Field002Chars00 ++ (fragment0122644Field003Chars00 ++ (fragment0122644Field004Chars00 ++ (tail))))))) fragment0122644Acc00000 := by rfl
    _ = SourceJson.object (fuel + 17) (SourceJson.white (fragment0122644Field001Chars00 ++ (fragment0122644Field002Chars00 ++ (fragment0122644Field003Chars00 ++ (fragment0122644Field004Chars00 ++ (tail)))))) fragment0122644Acc00100 := object_fragment0122644_field_000 fuel (fragment0122644Field001Chars00 ++ (fragment0122644Field002Chars00 ++ (fragment0122644Field003Chars00 ++ (fragment0122644Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 16) (SourceJson.white (fragment0122644Field002Chars00 ++ (fragment0122644Field003Chars00 ++ (fragment0122644Field004Chars00 ++ (tail))))) fragment0122644Acc00200 := object_fragment0122644_field_001 fuel (fragment0122644Field002Chars00 ++ (fragment0122644Field003Chars00 ++ (fragment0122644Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 15) (SourceJson.white (fragment0122644Field003Chars00 ++ (fragment0122644Field004Chars00 ++ (tail)))) fragment0122644Acc00300 := object_fragment0122644_field_002 fuel (fragment0122644Field003Chars00 ++ (fragment0122644Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 14) (SourceJson.white (fragment0122644Field004Chars00 ++ (tail))) fragment0122644Acc00400 := object_fragment0122644_field_003 fuel (fragment0122644Field004Chars00 ++ (tail))
    _ = .ok (fragment0122644Value, tail) := object_fragment0122644_field_004 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0048_before_reader"
  err.flush

noncomputable def chunk0048Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0048Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '6'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['4'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['1', '6'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['7']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '4'])], .arr [.number (String.ofList ['7']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '6'])], .arr [.number (String.ofList ['7']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '6'])], .arr [.number (String.ofList ['7']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '6'])], .arr [.number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '6'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['1']))]) :: (acc)

theorem array_chunk0048 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 24) (SourceJson.white (chunk0048Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 23) (SourceJson.white tail) (chunk0048Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0048_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0049_before_reader"
  err.flush

noncomputable def chunk0049LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0049SuffixChars00 : List Char := [',']
noncomputable def chunk0049Chars00 : List Char := chunk0049LeadChars00 ++ fragment0120838Chars ++ chunk0049SuffixChars00
noncomputable def chunk0049Push00 (acc : List SourceJson) : List SourceJson := fragment0120838Value :: acc

noncomputable def chunk0049AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0049_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 23)
      (SourceJson.white (chunk0049LeadChars00 ++ (fragment0120838Chars ++ rest))) acc =
      (SourceJson.value (fuel + 22) (fragment0120838Chars ++ rest)).bind
        (chunk0049AfterValue00 (fuel + 22) acc) := by rfl

theorem array_chunk0049 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 23) (SourceJson.white (chunk0049Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 22) (SourceJson.white tail) (chunk0049Push00 acc) := by
  have hinput : chunk0049Chars00 ++ tail = chunk0049LeadChars00 ++ (fragment0120838Chars ++ (chunk0049SuffixChars00 ++ tail)) := by
    simp only [chunk0049Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 23) (SourceJson.white (chunk0049Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 23)
          (SourceJson.white (chunk0049LeadChars00 ++ (fragment0120838Chars ++ (chunk0049SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 23) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 22) (fragment0120838Chars ++ (chunk0049SuffixChars00 ++ tail))).bind
        (chunk0049AfterValue00 (fuel + 22) acc) := array_chunk0049_head fuel (chunk0049SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0120838Value, chunk0049SuffixChars00 ++ tail)).bind
        (chunk0049AfterValue00 (fuel + 22) acc) :=
      congrArg (fun result => result.bind (chunk0049AfterValue00 (fuel + 22) acc))
        (value_fragment0120838 (fuel + 3) (chunk0049SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 22) (SourceJson.white tail) (chunk0049Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0049_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0050_before_reader"
  err.flush

noncomputable def chunk0050LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0050SuffixChars00 : List Char := [',']
noncomputable def chunk0050Chars00 : List Char := chunk0050LeadChars00 ++ fragment0121634Chars ++ chunk0050SuffixChars00
noncomputable def chunk0050Push00 (acc : List SourceJson) : List SourceJson := fragment0121634Value :: acc

noncomputable def chunk0050AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0050_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 22)
      (SourceJson.white (chunk0050LeadChars00 ++ (fragment0121634Chars ++ rest))) acc =
      (SourceJson.value (fuel + 21) (fragment0121634Chars ++ rest)).bind
        (chunk0050AfterValue00 (fuel + 21) acc) := by rfl

theorem array_chunk0050 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 22) (SourceJson.white (chunk0050Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 21) (SourceJson.white tail) (chunk0050Push00 acc) := by
  have hinput : chunk0050Chars00 ++ tail = chunk0050LeadChars00 ++ (fragment0121634Chars ++ (chunk0050SuffixChars00 ++ tail)) := by
    simp only [chunk0050Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 22) (SourceJson.white (chunk0050Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 22)
          (SourceJson.white (chunk0050LeadChars00 ++ (fragment0121634Chars ++ (chunk0050SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 22) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 21) (fragment0121634Chars ++ (chunk0050SuffixChars00 ++ tail))).bind
        (chunk0050AfterValue00 (fuel + 21) acc) := array_chunk0050_head fuel (chunk0050SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0121634Value, chunk0050SuffixChars00 ++ tail)).bind
        (chunk0050AfterValue00 (fuel + 21) acc) :=
      congrArg (fun result => result.bind (chunk0050AfterValue00 (fuel + 21) acc))
        (value_fragment0121634 (fuel + 0) (chunk0050SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 21) (SourceJson.white tail) (chunk0050Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0050_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0051_before_reader"
  err.flush

noncomputable def chunk0051LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0051SuffixChars00 : List Char := [',']
noncomputable def chunk0051Chars00 : List Char := chunk0051LeadChars00 ++ fragment0122644Chars ++ chunk0051SuffixChars00
noncomputable def chunk0051Push00 (acc : List SourceJson) : List SourceJson := fragment0122644Value :: acc

noncomputable def chunk0051AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0051_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 21)
      (SourceJson.white (chunk0051LeadChars00 ++ (fragment0122644Chars ++ rest))) acc =
      (SourceJson.value (fuel + 20) (fragment0122644Chars ++ rest)).bind
        (chunk0051AfterValue00 (fuel + 20) acc) := by rfl

theorem array_chunk0051 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 21) (SourceJson.white (chunk0051Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 20) (SourceJson.white tail) (chunk0051Push00 acc) := by
  have hinput : chunk0051Chars00 ++ tail = chunk0051LeadChars00 ++ (fragment0122644Chars ++ (chunk0051SuffixChars00 ++ tail)) := by
    simp only [chunk0051Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 21) (SourceJson.white (chunk0051Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 21)
          (SourceJson.white (chunk0051LeadChars00 ++ (fragment0122644Chars ++ (chunk0051SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 21) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 20) (fragment0122644Chars ++ (chunk0051SuffixChars00 ++ tail))).bind
        (chunk0051AfterValue00 (fuel + 20) acc) := array_chunk0051_head fuel (chunk0051SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0122644Value, chunk0051SuffixChars00 ++ tail)).bind
        (chunk0051AfterValue00 (fuel + 20) acc) :=
      congrArg (fun result => result.bind (chunk0051AfterValue00 (fuel + 20) acc))
        (value_fragment0122644 (fuel + 1) (chunk0051SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 20) (SourceJson.white tail) (chunk0051Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0051_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0052_before_reader"
  err.flush

noncomputable def chunk0052Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}', '\r', '\n', ' ', ' ', ']']
noncomputable def chunk0052Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['1', '4'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['1'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['1', '4'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['7'])], .arr [.number (String.ofList ['1', '4'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['1']))]) :: ((.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['7']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '4'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['2'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['1', '4'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['7']), .number (String.ofList ['1', '1'])], .arr [.number (String.ofList ['7']), .number (String.ofList ['1', '4'])], .arr [.number (String.ofList ['1', '1']), .number (String.ofList ['1', '4'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['1']))]) :: (acc))

theorem array_chunk0052 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 20) (SourceJson.white (chunk0052Chars00 ++ tail)) acc =
      .ok (.arr ((chunk0052Push00 acc).reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0052_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0048Chars00 ++ chunk0049Chars00 ++ chunk0050Chars00 ++ chunk0051Chars00 ++ chunk0052Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0052Push00 (chunk0051Push00 (chunk0050Push00 (chunk0049Push00 (chunk0048Push00 (acc)))))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 24) (SourceJson.white (blockChars ++ tail)) acc =
      .ok (.arr ((blockPush acc).reverse), tail) := by
  have hinput : blockChars ++ tail = chunk0048Chars00 ++ (chunk0049Chars00 ++ (chunk0050Chars00 ++ (chunk0051Chars00 ++ (chunk0052Chars00 ++ (tail))))) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 24) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 24) (SourceJson.white (chunk0048Chars00 ++ (chunk0049Chars00 ++ (chunk0050Chars00 ++ (chunk0051Chars00 ++ (chunk0052Chars00 ++ (tail))))))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 24) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 23) (SourceJson.white (chunk0049Chars00 ++ (chunk0050Chars00 ++ (chunk0051Chars00 ++ (chunk0052Chars00 ++ (tail)))))) (chunk0048Push00 (acc)) := array_chunk0048 fuel (chunk0049Chars00 ++ (chunk0050Chars00 ++ (chunk0051Chars00 ++ (chunk0052Chars00 ++ (tail))))) (acc)
    _ = SourceJson.array (fuel + 22) (SourceJson.white (chunk0050Chars00 ++ (chunk0051Chars00 ++ (chunk0052Chars00 ++ (tail))))) (chunk0049Push00 (chunk0048Push00 (acc))) := array_chunk0049 fuel (chunk0050Chars00 ++ (chunk0051Chars00 ++ (chunk0052Chars00 ++ (tail)))) (chunk0048Push00 (acc))
    _ = SourceJson.array (fuel + 21) (SourceJson.white (chunk0051Chars00 ++ (chunk0052Chars00 ++ (tail)))) (chunk0050Push00 (chunk0049Push00 (chunk0048Push00 (acc)))) := array_chunk0050 fuel (chunk0051Chars00 ++ (chunk0052Chars00 ++ (tail))) (chunk0049Push00 (chunk0048Push00 (acc)))
    _ = SourceJson.array (fuel + 20) (SourceJson.white (chunk0052Chars00 ++ (tail))) (chunk0051Push00 (chunk0050Push00 (chunk0049Push00 (chunk0048Push00 (acc))))) := array_chunk0051 fuel (chunk0052Chars00 ++ (tail)) (chunk0050Push00 (chunk0049Push00 (chunk0048Push00 (acc))))
    _ = .ok (.arr ((blockPush acc).reverse), tail) := array_chunk0052 fuel (tail) (chunk0051Push00 (chunk0050Push00 (chunk0049Push00 (chunk0048Push00 (acc)))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 120220).take 3792 = blockChars := by rfl

theorem block_original_split : sourceRest 120220 = blockChars ++ sourceRest 124012 := by
  calc
    sourceRest 120220 = (sourceRest 120220).take 3792 ++ (sourceRest 120220).drop 3792 :=
      (List.take_append_drop 3792 (sourceRest 120220)).symm
    _ = blockChars ++ (sourceRest 120220).drop 3792 :=
      congrArg (fun part => part ++ (sourceRest 120220).drop 3792) block_original_prefix
    _ = blockChars ++ sourceRest 124012 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 120220 3792)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 24) (SourceJson.white (sourceRest 120220)) acc =
      .ok (.arr ((blockPush acc).reverse), sourceRest 124012) :=
  (congrArg (fun chars => SourceJson.array (fuel + 24) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 124012) acc)

#print axioms object_fragment0120838_field_000
#print axioms object_fragment0120838_field_001
#print axioms object_fragment0120838_field_002
#print axioms object_fragment0120838_field_003
#print axioms object_fragment0120838_field_004
#print axioms value_fragment0120838
#print axioms array_fragment0121820_chunk_000
#print axioms array_fragment0121820_chunk_001
#print axioms array_fragment0121820_chunk_002
#print axioms array_fragment0121820_chunk_003
#print axioms value_fragment0121820
#print axioms object_fragment0121634_field_000
#print axioms object_fragment0121634_field_001
#print axioms object_fragment0121634_field_002
#print axioms object_fragment0121634_field_003_header
#print axioms object_fragment0121634_field_003
#print axioms object_fragment0121634_field_004
#print axioms value_fragment0121634
#print axioms object_fragment0122644_field_000
#print axioms object_fragment0122644_field_001
#print axioms object_fragment0122644_field_002
#print axioms object_fragment0122644_field_003
#print axioms object_fragment0122644_field_004
#print axioms value_fragment0122644
#print axioms array_chunk0048
#print axioms array_chunk0049_head
#print axioms array_chunk0049
#print axioms array_chunk0050_head
#print axioms array_chunk0050
#print axioms array_chunk0051_head
#print axioms array_chunk0051
#print axioms array_chunk0052
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end FaceLedgerBlock006

end ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing
