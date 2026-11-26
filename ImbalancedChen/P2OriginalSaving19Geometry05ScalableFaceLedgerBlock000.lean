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

namespace FaceLedgerBlock000

noncomputable def fragment0066820Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0066820Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0066820Field000Value00 : SourceJson := .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7'])]
noncomputable def fragment0066820Acc00100 : List (String × SourceJson) := (fragment0066820Field000Key00, fragment0066820Field000Value00) :: fragment0066820Acc00000
noncomputable def fragment0066820Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0066820_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 19) (SourceJson.white (fragment0066820Field000Chars00 ++ tail)) fragment0066820Acc00000 =
      SourceJson.object (fuel + 18) (SourceJson.white tail) fragment0066820Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0066820_object_field_000"
  err.flush

noncomputable def fragment0066820Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0066820Field001Value00 : SourceJson := .number (String.ofList ['4'])
noncomputable def fragment0066820Acc00200 : List (String × SourceJson) := (fragment0066820Field001Key00, fragment0066820Field001Value00) :: fragment0066820Acc00100
noncomputable def fragment0066820Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '4', ',']

theorem object_fragment0066820_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 18) (SourceJson.white (fragment0066820Field001Chars00 ++ tail)) fragment0066820Acc00100 =
      SourceJson.object (fuel + 17) (SourceJson.white tail) fragment0066820Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0066820_object_field_001"
  err.flush

noncomputable def fragment0066820Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0066820Field002Value00 : SourceJson := .number (String.ofList ['7'])
noncomputable def fragment0066820Acc00300 : List (String × SourceJson) := (fragment0066820Field002Key00, fragment0066820Field002Value00) :: fragment0066820Acc00200
noncomputable def fragment0066820Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '7', ',']

theorem object_fragment0066820_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 17) (SourceJson.white (fragment0066820Field002Chars00 ++ tail)) fragment0066820Acc00200 =
      SourceJson.object (fuel + 16) (SourceJson.white tail) fragment0066820Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0066820_object_field_002"
  err.flush

noncomputable def fragment0066820Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0066820Field003Value00 : SourceJson := .arr [.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['6']), .number (String.ofList ['7'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['6'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['7'])], .arr [.number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7'])]]
noncomputable def fragment0066820Acc00400 : List (String × SourceJson) := (fragment0066820Field003Key00, fragment0066820Field003Value00) :: fragment0066820Acc00300
noncomputable def fragment0066820Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0066820_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 16) (SourceJson.white (fragment0066820Field003Chars00 ++ tail)) fragment0066820Acc00300 =
      SourceJson.object (fuel + 15) (SourceJson.white tail) fragment0066820Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0066820_object_field_003"
  err.flush

noncomputable def fragment0066820Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0066820Field004Value00 : SourceJson := .number (String.ofList ['4'])
noncomputable def fragment0066820Acc00500 : List (String × SourceJson) := (fragment0066820Field004Key00, fragment0066820Field004Value00) :: fragment0066820Acc00400
noncomputable def fragment0066820Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0066820_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 15) (SourceJson.white (fragment0066820Field004Chars00 ++ tail)) fragment0066820Acc00400 =
      .ok (.obj (fragment0066820Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0066820_object_field_004"
  err.flush

noncomputable def fragment0066820Chars : List Char := '{' :: (fragment0066820Field000Chars00 ++ fragment0066820Field001Chars00 ++ fragment0066820Field002Chars00 ++ fragment0066820Field003Chars00 ++ fragment0066820Field004Chars00)
noncomputable def fragment0066820Value : SourceJson := .obj (fragment0066820Acc00500.reverse)

theorem value_fragment0066820 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 20) (fragment0066820Chars ++ tail) =
      .ok (fragment0066820Value, tail) := by
  have hinput : fragment0066820Chars ++ tail = '{' :: (fragment0066820Field000Chars00 ++ (fragment0066820Field001Chars00 ++ (fragment0066820Field002Chars00 ++ (fragment0066820Field003Chars00 ++ (fragment0066820Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0066820Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 20) (fragment0066820Chars ++ tail) =
        SourceJson.value (fuel + 20) ('{' :: (fragment0066820Field000Chars00 ++ (fragment0066820Field001Chars00 ++ (fragment0066820Field002Chars00 ++ (fragment0066820Field003Chars00 ++ (fragment0066820Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 20)) hinput
    _ = SourceJson.object (fuel + 19) (SourceJson.white (fragment0066820Field000Chars00 ++ (fragment0066820Field001Chars00 ++ (fragment0066820Field002Chars00 ++ (fragment0066820Field003Chars00 ++ (fragment0066820Field004Chars00 ++ (tail))))))) fragment0066820Acc00000 := by rfl
    _ = SourceJson.object (fuel + 18) (SourceJson.white (fragment0066820Field001Chars00 ++ (fragment0066820Field002Chars00 ++ (fragment0066820Field003Chars00 ++ (fragment0066820Field004Chars00 ++ (tail)))))) fragment0066820Acc00100 := object_fragment0066820_field_000 fuel (fragment0066820Field001Chars00 ++ (fragment0066820Field002Chars00 ++ (fragment0066820Field003Chars00 ++ (fragment0066820Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 17) (SourceJson.white (fragment0066820Field002Chars00 ++ (fragment0066820Field003Chars00 ++ (fragment0066820Field004Chars00 ++ (tail))))) fragment0066820Acc00200 := object_fragment0066820_field_001 fuel (fragment0066820Field002Chars00 ++ (fragment0066820Field003Chars00 ++ (fragment0066820Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 16) (SourceJson.white (fragment0066820Field003Chars00 ++ (fragment0066820Field004Chars00 ++ (tail)))) fragment0066820Acc00300 := object_fragment0066820_field_002 fuel (fragment0066820Field003Chars00 ++ (fragment0066820Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 15) (SourceJson.white (fragment0066820Field004Chars00 ++ (tail))) fragment0066820Acc00400 := object_fragment0066820_field_003 fuel (fragment0066820Field004Chars00 ++ (tail))
    _ = .ok (fragment0066820Value, tail) := object_fragment0066820_field_004 fuel (tail)

noncomputable def fragment0067852Acc00000 : List SourceJson := []

noncomputable def fragment0067852Chunk000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0067852Chunk000Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['8']), .number (String.ofList ['9'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7'])]) :: (acc))

theorem array_fragment0067852_chunk_000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 17) (SourceJson.white (fragment0067852Chunk000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 15) (SourceJson.white tail) (fragment0067852Chunk000Push00 acc) := by
  rfl

noncomputable def fragment0067852Acc00100 : List SourceJson := fragment0067852Chunk000Push00 fragment0067852Acc00000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0067852_array_chunk_000"
  err.flush

noncomputable def fragment0067852Chunk001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0067852Chunk001Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9'])]) :: (acc))

theorem array_fragment0067852_chunk_001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 15) (SourceJson.white (fragment0067852Chunk001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 13) (SourceJson.white tail) (fragment0067852Chunk001Push00 acc) := by
  rfl

noncomputable def fragment0067852Acc00200 : List SourceJson := fragment0067852Chunk001Push00 fragment0067852Acc00100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0067852_array_chunk_001"
  err.flush

noncomputable def fragment0067852Chunk002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0067852Chunk002Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['7']), .number (String.ofList ['8'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['6']), .number (String.ofList ['9'])]) :: (acc))

theorem array_fragment0067852_chunk_002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 13) (SourceJson.white (fragment0067852Chunk002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 11) (SourceJson.white tail) (fragment0067852Chunk002Push00 acc) := by
  rfl

noncomputable def fragment0067852Acc00300 : List SourceJson := fragment0067852Chunk002Push00 fragment0067852Acc00200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0067852_array_chunk_002"
  err.flush

noncomputable def fragment0067852Chunk003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']']
noncomputable def fragment0067852Chunk003Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9'])]) :: (acc)

theorem array_fragment0067852_chunk_003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 11) (SourceJson.white (fragment0067852Chunk003Chars00 ++ tail)) acc =
      .ok (.arr ((fragment0067852Chunk003Push00 acc).reverse), tail) := by
  rfl

noncomputable def fragment0067852Acc00400 : List SourceJson := fragment0067852Chunk003Push00 fragment0067852Acc00300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0067852_array_chunk_003"
  err.flush

noncomputable def fragment0067852Chars : List Char := '[' :: (fragment0067852Chunk000Chars00 ++ fragment0067852Chunk001Chars00 ++ fragment0067852Chunk002Chars00 ++ fragment0067852Chunk003Chars00)
noncomputable def fragment0067852Value : SourceJson := .arr (fragment0067852Acc00400.reverse)

theorem value_fragment0067852 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 18) (fragment0067852Chars ++ tail) =
      .ok (fragment0067852Value, tail) := by
  have hinput : fragment0067852Chars ++ tail = '[' :: (fragment0067852Chunk000Chars00 ++ (fragment0067852Chunk001Chars00 ++ (fragment0067852Chunk002Chars00 ++ (fragment0067852Chunk003Chars00 ++ (tail))))) := by
    simp only [fragment0067852Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 18) (fragment0067852Chars ++ tail) =
        SourceJson.value (fuel + 18) ('[' :: (fragment0067852Chunk000Chars00 ++ (fragment0067852Chunk001Chars00 ++ (fragment0067852Chunk002Chars00 ++ (fragment0067852Chunk003Chars00 ++ (tail)))))) :=
      congrArg (SourceJson.value (fuel + 18)) hinput
    _ = SourceJson.array (fuel + 17) (SourceJson.white (fragment0067852Chunk000Chars00 ++ (fragment0067852Chunk001Chars00 ++ (fragment0067852Chunk002Chars00 ++ (fragment0067852Chunk003Chars00 ++ (tail)))))) fragment0067852Acc00000 := by rfl
    _ = SourceJson.array (fuel + 15) (SourceJson.white (fragment0067852Chunk001Chars00 ++ (fragment0067852Chunk002Chars00 ++ (fragment0067852Chunk003Chars00 ++ (tail))))) fragment0067852Acc00100 := array_fragment0067852_chunk_000 fuel (fragment0067852Chunk001Chars00 ++ (fragment0067852Chunk002Chars00 ++ (fragment0067852Chunk003Chars00 ++ (tail)))) fragment0067852Acc00000
    _ = SourceJson.array (fuel + 13) (SourceJson.white (fragment0067852Chunk002Chars00 ++ (fragment0067852Chunk003Chars00 ++ (tail)))) fragment0067852Acc00200 := array_fragment0067852_chunk_001 fuel (fragment0067852Chunk002Chars00 ++ (fragment0067852Chunk003Chars00 ++ (tail))) fragment0067852Acc00100
    _ = SourceJson.array (fuel + 11) (SourceJson.white (fragment0067852Chunk003Chars00 ++ (tail))) fragment0067852Acc00300 := array_fragment0067852_chunk_002 fuel (fragment0067852Chunk003Chars00 ++ (tail)) fragment0067852Acc00200
    _ = .ok (fragment0067852Value, tail) := array_fragment0067852_chunk_003 fuel (tail) fragment0067852Acc00300

noncomputable def fragment0067637Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0067637Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0067637Field000Value00 : SourceJson := .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9'])]
noncomputable def fragment0067637Acc00100 : List (String × SourceJson) := (fragment0067637Field000Key00, fragment0067637Field000Value00) :: fragment0067637Acc00000
noncomputable def fragment0067637Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0067637_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 22) (SourceJson.white (fragment0067637Field000Chars00 ++ tail)) fragment0067637Acc00000 =
      SourceJson.object (fuel + 21) (SourceJson.white tail) fragment0067637Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0067637_object_field_000"
  err.flush

noncomputable def fragment0067637Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0067637Field001Value00 : SourceJson := .number (String.ofList ['5'])
noncomputable def fragment0067637Acc00200 : List (String × SourceJson) := (fragment0067637Field001Key00, fragment0067637Field001Value00) :: fragment0067637Acc00100
noncomputable def fragment0067637Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '5', ',']

theorem object_fragment0067637_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 21) (SourceJson.white (fragment0067637Field001Chars00 ++ tail)) fragment0067637Acc00100 =
      SourceJson.object (fuel + 20) (SourceJson.white tail) fragment0067637Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0067637_object_field_001"
  err.flush

noncomputable def fragment0067637Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0067637Field002Value00 : SourceJson := .number (String.ofList ['9'])
noncomputable def fragment0067637Acc00300 : List (String × SourceJson) := (fragment0067637Field002Key00, fragment0067637Field002Value00) :: fragment0067637Acc00200
noncomputable def fragment0067637Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '9', ',']

theorem object_fragment0067637_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 20) (SourceJson.white (fragment0067637Field002Chars00 ++ tail)) fragment0067637Acc00200 =
      SourceJson.object (fuel + 19) (SourceJson.white tail) fragment0067637Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0067637_object_field_002"
  err.flush

noncomputable def fragment0067637Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0067637Field003Value00 : SourceJson := fragment0067852Value
noncomputable def fragment0067637Acc00400 : List (String × SourceJson) := (fragment0067637Field003Key00, fragment0067637Field003Value00) :: fragment0067637Acc00300
noncomputable def fragment0067637Field003HeaderChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ']
noncomputable def fragment0067637Field003SuffixChars00 : List Char := [',']
noncomputable def fragment0067637Field003Chars00 : List Char := fragment0067637Field003HeaderChars00 ++ fragment0067852Chars ++ fragment0067637Field003SuffixChars00

noncomputable def fragment0067637Field003AfterValue00 (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending => .ok (.obj (((fragment0067637Field003Key00, result.1) :: fragment0067637Acc00300).reverse), ending)
  | ',' :: ending => SourceJson.object fuel (SourceJson.white ending) ((fragment0067637Field003Key00, result.1) :: fragment0067637Acc00300)
  | _ => .error "object separator missing"

theorem object_fragment0067637_field_003_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 19) (SourceJson.white (fragment0067637Field003HeaderChars00 ++ rest)) fragment0067637Acc00300 =
      (SourceJson.value (fuel + 18) rest).bind (fragment0067637Field003AfterValue00 (fuel + 18)) := by rfl

theorem object_fragment0067637_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 19) (SourceJson.white (fragment0067637Field003Chars00 ++ tail)) fragment0067637Acc00300 =
      SourceJson.object (fuel + 18) (SourceJson.white tail) fragment0067637Acc00400 := by
  have hinput : fragment0067637Field003Chars00 ++ tail = fragment0067637Field003HeaderChars00 ++ (fragment0067852Chars ++ (fragment0067637Field003SuffixChars00 ++ tail)) := by
    simp only [fragment0067637Field003Chars00, List.append_assoc]
  calc
    SourceJson.object (fuel + 19) (SourceJson.white (fragment0067637Field003Chars00 ++ tail)) fragment0067637Acc00300 =
        SourceJson.object (fuel + 19)
          (SourceJson.white (fragment0067637Field003HeaderChars00 ++ (fragment0067852Chars ++ (fragment0067637Field003SuffixChars00 ++ tail)))) fragment0067637Acc00300 :=
      congrArg (fun s => SourceJson.object (fuel + 19) (SourceJson.white s) fragment0067637Acc00300) hinput
    _ = (SourceJson.value (fuel + 18) (fragment0067852Chars ++ (fragment0067637Field003SuffixChars00 ++ tail))).bind
        (fragment0067637Field003AfterValue00 (fuel + 18)) := object_fragment0067637_field_003_header fuel (fragment0067852Chars ++ (fragment0067637Field003SuffixChars00 ++ tail))
    _ = (Except.ok (fragment0067852Value, fragment0067637Field003SuffixChars00 ++ tail)).bind (fragment0067637Field003AfterValue00 (fuel + 18)) :=
      congrArg (fun result => result.bind (fragment0067637Field003AfterValue00 (fuel + 18)))
        (value_fragment0067852 (fuel + 0) (fragment0067637Field003SuffixChars00 ++ tail))
    _ = SourceJson.object (fuel + 18) (SourceJson.white tail) fragment0067637Acc00400 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0067637_object_field_003"
  err.flush

noncomputable def fragment0067637Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0067637Field004Value00 : SourceJson := .number (String.ofList ['5'])
noncomputable def fragment0067637Acc00500 : List (String × SourceJson) := (fragment0067637Field004Key00, fragment0067637Field004Value00) :: fragment0067637Acc00400
noncomputable def fragment0067637Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '5', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0067637_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 18) (SourceJson.white (fragment0067637Field004Chars00 ++ tail)) fragment0067637Acc00400 =
      .ok (.obj (fragment0067637Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0067637_object_field_004"
  err.flush

noncomputable def fragment0067637Chars : List Char := '{' :: (fragment0067637Field000Chars00 ++ fragment0067637Field001Chars00 ++ fragment0067637Field002Chars00 ++ fragment0067637Field003Chars00 ++ fragment0067637Field004Chars00)
noncomputable def fragment0067637Value : SourceJson := .obj (fragment0067637Acc00500.reverse)

theorem value_fragment0067637 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 23) (fragment0067637Chars ++ tail) =
      .ok (fragment0067637Value, tail) := by
  have hinput : fragment0067637Chars ++ tail = '{' :: (fragment0067637Field000Chars00 ++ (fragment0067637Field001Chars00 ++ (fragment0067637Field002Chars00 ++ (fragment0067637Field003Chars00 ++ (fragment0067637Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0067637Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 23) (fragment0067637Chars ++ tail) =
        SourceJson.value (fuel + 23) ('{' :: (fragment0067637Field000Chars00 ++ (fragment0067637Field001Chars00 ++ (fragment0067637Field002Chars00 ++ (fragment0067637Field003Chars00 ++ (fragment0067637Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 23)) hinput
    _ = SourceJson.object (fuel + 22) (SourceJson.white (fragment0067637Field000Chars00 ++ (fragment0067637Field001Chars00 ++ (fragment0067637Field002Chars00 ++ (fragment0067637Field003Chars00 ++ (fragment0067637Field004Chars00 ++ (tail))))))) fragment0067637Acc00000 := by rfl
    _ = SourceJson.object (fuel + 21) (SourceJson.white (fragment0067637Field001Chars00 ++ (fragment0067637Field002Chars00 ++ (fragment0067637Field003Chars00 ++ (fragment0067637Field004Chars00 ++ (tail)))))) fragment0067637Acc00100 := object_fragment0067637_field_000 fuel (fragment0067637Field001Chars00 ++ (fragment0067637Field002Chars00 ++ (fragment0067637Field003Chars00 ++ (fragment0067637Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 20) (SourceJson.white (fragment0067637Field002Chars00 ++ (fragment0067637Field003Chars00 ++ (fragment0067637Field004Chars00 ++ (tail))))) fragment0067637Acc00200 := object_fragment0067637_field_001 fuel (fragment0067637Field002Chars00 ++ (fragment0067637Field003Chars00 ++ (fragment0067637Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 19) (SourceJson.white (fragment0067637Field003Chars00 ++ (fragment0067637Field004Chars00 ++ (tail)))) fragment0067637Acc00300 := object_fragment0067637_field_002 fuel (fragment0067637Field003Chars00 ++ (fragment0067637Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 18) (SourceJson.white (fragment0067637Field004Chars00 ++ (tail))) fragment0067637Acc00400 := object_fragment0067637_field_003 fuel (fragment0067637Field004Chars00 ++ (tail))
    _ = .ok (fragment0067637Value, tail) := object_fragment0067637_field_004 fuel (tail)

noncomputable def fragment0068994Acc00000 : List SourceJson := []

noncomputable def fragment0068994Chunk000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0068994Chunk000Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9'])]) :: (acc))

theorem array_fragment0068994_chunk_000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 20) (SourceJson.white (fragment0068994Chunk000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 18) (SourceJson.white tail) (fragment0068994Chunk000Push00 acc) := by
  rfl

noncomputable def fragment0068994Acc00100 : List SourceJson := fragment0068994Chunk000Push00 fragment0068994Acc00000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0068994_array_chunk_000"
  err.flush

noncomputable def fragment0068994Chunk001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0068994Chunk001Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1'])]) :: (acc))

theorem array_fragment0068994_chunk_001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 18) (SourceJson.white (fragment0068994Chunk001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 16) (SourceJson.white tail) (fragment0068994Chunk001Push00 acc) := by
  rfl

noncomputable def fragment0068994Acc00200 : List SourceJson := fragment0068994Chunk001Push00 fragment0068994Acc00100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0068994_array_chunk_001"
  err.flush

noncomputable def fragment0068994Chunk002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0068994Chunk002Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['6']), .number (String.ofList ['9']), .number (String.ofList ['1', '1'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1'])]) :: (acc))

theorem array_fragment0068994_chunk_002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 16) (SourceJson.white (fragment0068994Chunk002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 14) (SourceJson.white tail) (fragment0068994Chunk002Push00 acc) := by
  rfl

noncomputable def fragment0068994Acc00300 : List SourceJson := fragment0068994Chunk002Push00 fragment0068994Acc00200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0068994_array_chunk_002"
  err.flush

noncomputable def fragment0068994Chunk003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']']
noncomputable def fragment0068994Chunk003Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1'])]) :: ((.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '0'])]) :: (acc))

theorem array_fragment0068994_chunk_003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 14) (SourceJson.white (fragment0068994Chunk003Chars00 ++ tail)) acc =
      .ok (.arr ((fragment0068994Chunk003Push00 acc).reverse), tail) := by
  rfl

noncomputable def fragment0068994Acc00400 : List SourceJson := fragment0068994Chunk003Push00 fragment0068994Acc00300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0068994_array_chunk_003"
  err.flush

noncomputable def fragment0068994Chars : List Char := '[' :: (fragment0068994Chunk000Chars00 ++ fragment0068994Chunk001Chars00 ++ fragment0068994Chunk002Chars00 ++ fragment0068994Chunk003Chars00)
noncomputable def fragment0068994Value : SourceJson := .arr (fragment0068994Acc00400.reverse)

theorem value_fragment0068994 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 21) (fragment0068994Chars ++ tail) =
      .ok (fragment0068994Value, tail) := by
  have hinput : fragment0068994Chars ++ tail = '[' :: (fragment0068994Chunk000Chars00 ++ (fragment0068994Chunk001Chars00 ++ (fragment0068994Chunk002Chars00 ++ (fragment0068994Chunk003Chars00 ++ (tail))))) := by
    simp only [fragment0068994Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 21) (fragment0068994Chars ++ tail) =
        SourceJson.value (fuel + 21) ('[' :: (fragment0068994Chunk000Chars00 ++ (fragment0068994Chunk001Chars00 ++ (fragment0068994Chunk002Chars00 ++ (fragment0068994Chunk003Chars00 ++ (tail)))))) :=
      congrArg (SourceJson.value (fuel + 21)) hinput
    _ = SourceJson.array (fuel + 20) (SourceJson.white (fragment0068994Chunk000Chars00 ++ (fragment0068994Chunk001Chars00 ++ (fragment0068994Chunk002Chars00 ++ (fragment0068994Chunk003Chars00 ++ (tail)))))) fragment0068994Acc00000 := by rfl
    _ = SourceJson.array (fuel + 18) (SourceJson.white (fragment0068994Chunk001Chars00 ++ (fragment0068994Chunk002Chars00 ++ (fragment0068994Chunk003Chars00 ++ (tail))))) fragment0068994Acc00100 := array_fragment0068994_chunk_000 fuel (fragment0068994Chunk001Chars00 ++ (fragment0068994Chunk002Chars00 ++ (fragment0068994Chunk003Chars00 ++ (tail)))) fragment0068994Acc00000
    _ = SourceJson.array (fuel + 16) (SourceJson.white (fragment0068994Chunk002Chars00 ++ (fragment0068994Chunk003Chars00 ++ (tail)))) fragment0068994Acc00200 := array_fragment0068994_chunk_001 fuel (fragment0068994Chunk002Chars00 ++ (fragment0068994Chunk003Chars00 ++ (tail))) fragment0068994Acc00100
    _ = SourceJson.array (fuel + 14) (SourceJson.white (fragment0068994Chunk003Chars00 ++ (tail))) fragment0068994Acc00300 := array_fragment0068994_chunk_002 fuel (fragment0068994Chunk003Chars00 ++ (tail)) fragment0068994Acc00200
    _ = .ok (fragment0068994Value, tail) := array_fragment0068994_chunk_003 fuel (tail) fragment0068994Acc00300

noncomputable def fragment0068752Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0068752Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0068752Field000Value00 : SourceJson := .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1'])]
noncomputable def fragment0068752Acc00100 : List (String × SourceJson) := (fragment0068752Field000Key00, fragment0068752Field000Value00) :: fragment0068752Acc00000
noncomputable def fragment0068752Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0068752_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 25) (SourceJson.white (fragment0068752Field000Chars00 ++ tail)) fragment0068752Acc00000 =
      SourceJson.object (fuel + 24) (SourceJson.white tail) fragment0068752Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0068752_object_field_000"
  err.flush

noncomputable def fragment0068752Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0068752Field001Value00 : SourceJson := .number (String.ofList ['6'])
noncomputable def fragment0068752Acc00200 : List (String × SourceJson) := (fragment0068752Field001Key00, fragment0068752Field001Value00) :: fragment0068752Acc00100
noncomputable def fragment0068752Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '6', ',']

theorem object_fragment0068752_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 24) (SourceJson.white (fragment0068752Field001Chars00 ++ tail)) fragment0068752Acc00100 =
      SourceJson.object (fuel + 23) (SourceJson.white tail) fragment0068752Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0068752_object_field_001"
  err.flush

noncomputable def fragment0068752Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0068752Field002Value00 : SourceJson := .number (String.ofList ['1', '1'])
noncomputable def fragment0068752Acc00300 : List (String × SourceJson) := (fragment0068752Field002Key00, fragment0068752Field002Value00) :: fragment0068752Acc00200
noncomputable def fragment0068752Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '1', '1', ',']

theorem object_fragment0068752_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 23) (SourceJson.white (fragment0068752Field002Chars00 ++ tail)) fragment0068752Acc00200 =
      SourceJson.object (fuel + 22) (SourceJson.white tail) fragment0068752Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0068752_object_field_002"
  err.flush

noncomputable def fragment0068752Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0068752Field003Value00 : SourceJson := fragment0068994Value
noncomputable def fragment0068752Acc00400 : List (String × SourceJson) := (fragment0068752Field003Key00, fragment0068752Field003Value00) :: fragment0068752Acc00300
noncomputable def fragment0068752Field003HeaderChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ']
noncomputable def fragment0068752Field003SuffixChars00 : List Char := [',']
noncomputable def fragment0068752Field003Chars00 : List Char := fragment0068752Field003HeaderChars00 ++ fragment0068994Chars ++ fragment0068752Field003SuffixChars00

noncomputable def fragment0068752Field003AfterValue00 (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending => .ok (.obj (((fragment0068752Field003Key00, result.1) :: fragment0068752Acc00300).reverse), ending)
  | ',' :: ending => SourceJson.object fuel (SourceJson.white ending) ((fragment0068752Field003Key00, result.1) :: fragment0068752Acc00300)
  | _ => .error "object separator missing"

theorem object_fragment0068752_field_003_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 22) (SourceJson.white (fragment0068752Field003HeaderChars00 ++ rest)) fragment0068752Acc00300 =
      (SourceJson.value (fuel + 21) rest).bind (fragment0068752Field003AfterValue00 (fuel + 21)) := by rfl

theorem object_fragment0068752_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 22) (SourceJson.white (fragment0068752Field003Chars00 ++ tail)) fragment0068752Acc00300 =
      SourceJson.object (fuel + 21) (SourceJson.white tail) fragment0068752Acc00400 := by
  have hinput : fragment0068752Field003Chars00 ++ tail = fragment0068752Field003HeaderChars00 ++ (fragment0068994Chars ++ (fragment0068752Field003SuffixChars00 ++ tail)) := by
    simp only [fragment0068752Field003Chars00, List.append_assoc]
  calc
    SourceJson.object (fuel + 22) (SourceJson.white (fragment0068752Field003Chars00 ++ tail)) fragment0068752Acc00300 =
        SourceJson.object (fuel + 22)
          (SourceJson.white (fragment0068752Field003HeaderChars00 ++ (fragment0068994Chars ++ (fragment0068752Field003SuffixChars00 ++ tail)))) fragment0068752Acc00300 :=
      congrArg (fun s => SourceJson.object (fuel + 22) (SourceJson.white s) fragment0068752Acc00300) hinput
    _ = (SourceJson.value (fuel + 21) (fragment0068994Chars ++ (fragment0068752Field003SuffixChars00 ++ tail))).bind
        (fragment0068752Field003AfterValue00 (fuel + 21)) := object_fragment0068752_field_003_header fuel (fragment0068994Chars ++ (fragment0068752Field003SuffixChars00 ++ tail))
    _ = (Except.ok (fragment0068994Value, fragment0068752Field003SuffixChars00 ++ tail)).bind (fragment0068752Field003AfterValue00 (fuel + 21)) :=
      congrArg (fun result => result.bind (fragment0068752Field003AfterValue00 (fuel + 21)))
        (value_fragment0068994 (fuel + 0) (fragment0068752Field003SuffixChars00 ++ tail))
    _ = SourceJson.object (fuel + 21) (SourceJson.white tail) fragment0068752Acc00400 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0068752_object_field_003"
  err.flush

noncomputable def fragment0068752Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0068752Field004Value00 : SourceJson := .number (String.ofList ['6'])
noncomputable def fragment0068752Acc00500 : List (String × SourceJson) := (fragment0068752Field004Key00, fragment0068752Field004Value00) :: fragment0068752Acc00400
noncomputable def fragment0068752Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '6', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0068752_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 21) (SourceJson.white (fragment0068752Field004Chars00 ++ tail)) fragment0068752Acc00400 =
      .ok (.obj (fragment0068752Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0068752_object_field_004"
  err.flush

noncomputable def fragment0068752Chars : List Char := '{' :: (fragment0068752Field000Chars00 ++ fragment0068752Field001Chars00 ++ fragment0068752Field002Chars00 ++ fragment0068752Field003Chars00 ++ fragment0068752Field004Chars00)
noncomputable def fragment0068752Value : SourceJson := .obj (fragment0068752Acc00500.reverse)

theorem value_fragment0068752 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 26) (fragment0068752Chars ++ tail) =
      .ok (fragment0068752Value, tail) := by
  have hinput : fragment0068752Chars ++ tail = '{' :: (fragment0068752Field000Chars00 ++ (fragment0068752Field001Chars00 ++ (fragment0068752Field002Chars00 ++ (fragment0068752Field003Chars00 ++ (fragment0068752Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0068752Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 26) (fragment0068752Chars ++ tail) =
        SourceJson.value (fuel + 26) ('{' :: (fragment0068752Field000Chars00 ++ (fragment0068752Field001Chars00 ++ (fragment0068752Field002Chars00 ++ (fragment0068752Field003Chars00 ++ (fragment0068752Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 26)) hinput
    _ = SourceJson.object (fuel + 25) (SourceJson.white (fragment0068752Field000Chars00 ++ (fragment0068752Field001Chars00 ++ (fragment0068752Field002Chars00 ++ (fragment0068752Field003Chars00 ++ (fragment0068752Field004Chars00 ++ (tail))))))) fragment0068752Acc00000 := by rfl
    _ = SourceJson.object (fuel + 24) (SourceJson.white (fragment0068752Field001Chars00 ++ (fragment0068752Field002Chars00 ++ (fragment0068752Field003Chars00 ++ (fragment0068752Field004Chars00 ++ (tail)))))) fragment0068752Acc00100 := object_fragment0068752_field_000 fuel (fragment0068752Field001Chars00 ++ (fragment0068752Field002Chars00 ++ (fragment0068752Field003Chars00 ++ (fragment0068752Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 23) (SourceJson.white (fragment0068752Field002Chars00 ++ (fragment0068752Field003Chars00 ++ (fragment0068752Field004Chars00 ++ (tail))))) fragment0068752Acc00200 := object_fragment0068752_field_001 fuel (fragment0068752Field002Chars00 ++ (fragment0068752Field003Chars00 ++ (fragment0068752Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 22) (SourceJson.white (fragment0068752Field003Chars00 ++ (fragment0068752Field004Chars00 ++ (tail)))) fragment0068752Acc00300 := object_fragment0068752_field_002 fuel (fragment0068752Field003Chars00 ++ (fragment0068752Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 21) (SourceJson.white (fragment0068752Field004Chars00 ++ (tail))) fragment0068752Acc00400 := object_fragment0068752_field_003 fuel (fragment0068752Field004Chars00 ++ (tail))
    _ = .ok (fragment0068752Value, tail) := object_fragment0068752_field_004 fuel (tail)

noncomputable def fragment0070504Acc00000 : List SourceJson := []

noncomputable def fragment0070504Chunk000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0070504Chunk000Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1'])]) :: (acc))

theorem array_fragment0070504_chunk_000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 23) (SourceJson.white (fragment0070504Chunk000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 21) (SourceJson.white tail) (fragment0070504Chunk000Push00 acc) := by
  rfl

noncomputable def fragment0070504Acc00100 : List SourceJson := fragment0070504Chunk000Push00 fragment0070504Acc00000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0070504_array_chunk_000"
  err.flush

noncomputable def fragment0070504Chunk001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0070504Chunk001Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3'])]) :: (acc))

theorem array_fragment0070504_chunk_001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 21) (SourceJson.white (fragment0070504Chunk001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 19) (SourceJson.white tail) (fragment0070504Chunk001Push00 acc) := by
  rfl

noncomputable def fragment0070504Acc00200 : List SourceJson := fragment0070504Chunk001Push00 fragment0070504Acc00100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0070504_array_chunk_001"
  err.flush

noncomputable def fragment0070504Chunk002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0070504Chunk002Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3'])]) :: (acc))

theorem array_fragment0070504_chunk_002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 19) (SourceJson.white (fragment0070504Chunk002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 17) (SourceJson.white tail) (fragment0070504Chunk002Push00 acc) := by
  rfl

noncomputable def fragment0070504Acc00300 : List SourceJson := fragment0070504Chunk002Push00 fragment0070504Acc00200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0070504_array_chunk_002"
  err.flush

noncomputable def fragment0070504Chunk003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0070504Chunk003Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '2'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['6']), .number (String.ofList ['9']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '3'])]) :: (acc))

theorem array_fragment0070504_chunk_003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 17) (SourceJson.white (fragment0070504Chunk003Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 15) (SourceJson.white tail) (fragment0070504Chunk003Push00 acc) := by
  rfl

noncomputable def fragment0070504Acc00400 : List SourceJson := fragment0070504Chunk003Push00 fragment0070504Acc00300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0070504_array_chunk_003"
  err.flush

noncomputable def fragment0070504Chunk004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']']
noncomputable def fragment0070504Chunk004Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3'])]) :: (acc)

theorem array_fragment0070504_chunk_004 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 15) (SourceJson.white (fragment0070504Chunk004Chars00 ++ tail)) acc =
      .ok (.arr ((fragment0070504Chunk004Push00 acc).reverse), tail) := by
  rfl

noncomputable def fragment0070504Acc00500 : List SourceJson := fragment0070504Chunk004Push00 fragment0070504Acc00400

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0070504_array_chunk_004"
  err.flush

noncomputable def fragment0070504Chars : List Char := '[' :: (fragment0070504Chunk000Chars00 ++ fragment0070504Chunk001Chars00 ++ fragment0070504Chunk002Chars00 ++ fragment0070504Chunk003Chars00 ++ fragment0070504Chunk004Chars00)
noncomputable def fragment0070504Value : SourceJson := .arr (fragment0070504Acc00500.reverse)

theorem value_fragment0070504 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 24) (fragment0070504Chars ++ tail) =
      .ok (fragment0070504Value, tail) := by
  have hinput : fragment0070504Chars ++ tail = '[' :: (fragment0070504Chunk000Chars00 ++ (fragment0070504Chunk001Chars00 ++ (fragment0070504Chunk002Chars00 ++ (fragment0070504Chunk003Chars00 ++ (fragment0070504Chunk004Chars00 ++ (tail)))))) := by
    simp only [fragment0070504Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 24) (fragment0070504Chars ++ tail) =
        SourceJson.value (fuel + 24) ('[' :: (fragment0070504Chunk000Chars00 ++ (fragment0070504Chunk001Chars00 ++ (fragment0070504Chunk002Chars00 ++ (fragment0070504Chunk003Chars00 ++ (fragment0070504Chunk004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 24)) hinput
    _ = SourceJson.array (fuel + 23) (SourceJson.white (fragment0070504Chunk000Chars00 ++ (fragment0070504Chunk001Chars00 ++ (fragment0070504Chunk002Chars00 ++ (fragment0070504Chunk003Chars00 ++ (fragment0070504Chunk004Chars00 ++ (tail))))))) fragment0070504Acc00000 := by rfl
    _ = SourceJson.array (fuel + 21) (SourceJson.white (fragment0070504Chunk001Chars00 ++ (fragment0070504Chunk002Chars00 ++ (fragment0070504Chunk003Chars00 ++ (fragment0070504Chunk004Chars00 ++ (tail)))))) fragment0070504Acc00100 := array_fragment0070504_chunk_000 fuel (fragment0070504Chunk001Chars00 ++ (fragment0070504Chunk002Chars00 ++ (fragment0070504Chunk003Chars00 ++ (fragment0070504Chunk004Chars00 ++ (tail))))) fragment0070504Acc00000
    _ = SourceJson.array (fuel + 19) (SourceJson.white (fragment0070504Chunk002Chars00 ++ (fragment0070504Chunk003Chars00 ++ (fragment0070504Chunk004Chars00 ++ (tail))))) fragment0070504Acc00200 := array_fragment0070504_chunk_001 fuel (fragment0070504Chunk002Chars00 ++ (fragment0070504Chunk003Chars00 ++ (fragment0070504Chunk004Chars00 ++ (tail)))) fragment0070504Acc00100
    _ = SourceJson.array (fuel + 17) (SourceJson.white (fragment0070504Chunk003Chars00 ++ (fragment0070504Chunk004Chars00 ++ (tail)))) fragment0070504Acc00300 := array_fragment0070504_chunk_002 fuel (fragment0070504Chunk003Chars00 ++ (fragment0070504Chunk004Chars00 ++ (tail))) fragment0070504Acc00200
    _ = SourceJson.array (fuel + 15) (SourceJson.white (fragment0070504Chunk004Chars00 ++ (tail))) fragment0070504Acc00400 := array_fragment0070504_chunk_003 fuel (fragment0070504Chunk004Chars00 ++ (tail)) fragment0070504Acc00300
    _ = .ok (fragment0070504Value, tail) := array_fragment0070504_chunk_004 fuel (tail) fragment0070504Acc00400

noncomputable def fragment0070236Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0070236Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0070236Field000Value00 : SourceJson := .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3'])]
noncomputable def fragment0070236Acc00100 : List (String × SourceJson) := (fragment0070236Field000Key00, fragment0070236Field000Value00) :: fragment0070236Acc00000
noncomputable def fragment0070236Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0070236_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 28) (SourceJson.white (fragment0070236Field000Chars00 ++ tail)) fragment0070236Acc00000 =
      SourceJson.object (fuel + 27) (SourceJson.white tail) fragment0070236Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0070236_object_field_000"
  err.flush

noncomputable def fragment0070236Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0070236Field001Value00 : SourceJson := .number (String.ofList ['7'])
noncomputable def fragment0070236Acc00200 : List (String × SourceJson) := (fragment0070236Field001Key00, fragment0070236Field001Value00) :: fragment0070236Acc00100
noncomputable def fragment0070236Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '7', ',']

theorem object_fragment0070236_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 27) (SourceJson.white (fragment0070236Field001Chars00 ++ tail)) fragment0070236Acc00100 =
      SourceJson.object (fuel + 26) (SourceJson.white tail) fragment0070236Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0070236_object_field_001"
  err.flush

noncomputable def fragment0070236Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0070236Field002Value00 : SourceJson := .number (String.ofList ['1', '3'])
noncomputable def fragment0070236Acc00300 : List (String × SourceJson) := (fragment0070236Field002Key00, fragment0070236Field002Value00) :: fragment0070236Acc00200
noncomputable def fragment0070236Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '1', '3', ',']

theorem object_fragment0070236_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 26) (SourceJson.white (fragment0070236Field002Chars00 ++ tail)) fragment0070236Acc00200 =
      SourceJson.object (fuel + 25) (SourceJson.white tail) fragment0070236Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0070236_object_field_002"
  err.flush

noncomputable def fragment0070236Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0070236Field003Value00 : SourceJson := fragment0070504Value
noncomputable def fragment0070236Acc00400 : List (String × SourceJson) := (fragment0070236Field003Key00, fragment0070236Field003Value00) :: fragment0070236Acc00300
noncomputable def fragment0070236Field003HeaderChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ']
noncomputable def fragment0070236Field003SuffixChars00 : List Char := [',']
noncomputable def fragment0070236Field003Chars00 : List Char := fragment0070236Field003HeaderChars00 ++ fragment0070504Chars ++ fragment0070236Field003SuffixChars00

noncomputable def fragment0070236Field003AfterValue00 (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending => .ok (.obj (((fragment0070236Field003Key00, result.1) :: fragment0070236Acc00300).reverse), ending)
  | ',' :: ending => SourceJson.object fuel (SourceJson.white ending) ((fragment0070236Field003Key00, result.1) :: fragment0070236Acc00300)
  | _ => .error "object separator missing"

theorem object_fragment0070236_field_003_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 25) (SourceJson.white (fragment0070236Field003HeaderChars00 ++ rest)) fragment0070236Acc00300 =
      (SourceJson.value (fuel + 24) rest).bind (fragment0070236Field003AfterValue00 (fuel + 24)) := by rfl

theorem object_fragment0070236_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 25) (SourceJson.white (fragment0070236Field003Chars00 ++ tail)) fragment0070236Acc00300 =
      SourceJson.object (fuel + 24) (SourceJson.white tail) fragment0070236Acc00400 := by
  have hinput : fragment0070236Field003Chars00 ++ tail = fragment0070236Field003HeaderChars00 ++ (fragment0070504Chars ++ (fragment0070236Field003SuffixChars00 ++ tail)) := by
    simp only [fragment0070236Field003Chars00, List.append_assoc]
  calc
    SourceJson.object (fuel + 25) (SourceJson.white (fragment0070236Field003Chars00 ++ tail)) fragment0070236Acc00300 =
        SourceJson.object (fuel + 25)
          (SourceJson.white (fragment0070236Field003HeaderChars00 ++ (fragment0070504Chars ++ (fragment0070236Field003SuffixChars00 ++ tail)))) fragment0070236Acc00300 :=
      congrArg (fun s => SourceJson.object (fuel + 25) (SourceJson.white s) fragment0070236Acc00300) hinput
    _ = (SourceJson.value (fuel + 24) (fragment0070504Chars ++ (fragment0070236Field003SuffixChars00 ++ tail))).bind
        (fragment0070236Field003AfterValue00 (fuel + 24)) := object_fragment0070236_field_003_header fuel (fragment0070504Chars ++ (fragment0070236Field003SuffixChars00 ++ tail))
    _ = (Except.ok (fragment0070504Value, fragment0070236Field003SuffixChars00 ++ tail)).bind (fragment0070236Field003AfterValue00 (fuel + 24)) :=
      congrArg (fun result => result.bind (fragment0070236Field003AfterValue00 (fuel + 24)))
        (value_fragment0070504 (fuel + 0) (fragment0070236Field003SuffixChars00 ++ tail))
    _ = SourceJson.object (fuel + 24) (SourceJson.white tail) fragment0070236Acc00400 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0070236_object_field_003"
  err.flush

noncomputable def fragment0070236Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0070236Field004Value00 : SourceJson := .number (String.ofList ['7'])
noncomputable def fragment0070236Acc00500 : List (String × SourceJson) := (fragment0070236Field004Key00, fragment0070236Field004Value00) :: fragment0070236Acc00400
noncomputable def fragment0070236Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '7', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0070236_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 24) (SourceJson.white (fragment0070236Field004Chars00 ++ tail)) fragment0070236Acc00400 =
      .ok (.obj (fragment0070236Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0070236_object_field_004"
  err.flush

noncomputable def fragment0070236Chars : List Char := '{' :: (fragment0070236Field000Chars00 ++ fragment0070236Field001Chars00 ++ fragment0070236Field002Chars00 ++ fragment0070236Field003Chars00 ++ fragment0070236Field004Chars00)
noncomputable def fragment0070236Value : SourceJson := .obj (fragment0070236Acc00500.reverse)

theorem value_fragment0070236 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 29) (fragment0070236Chars ++ tail) =
      .ok (fragment0070236Value, tail) := by
  have hinput : fragment0070236Chars ++ tail = '{' :: (fragment0070236Field000Chars00 ++ (fragment0070236Field001Chars00 ++ (fragment0070236Field002Chars00 ++ (fragment0070236Field003Chars00 ++ (fragment0070236Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0070236Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 29) (fragment0070236Chars ++ tail) =
        SourceJson.value (fuel + 29) ('{' :: (fragment0070236Field000Chars00 ++ (fragment0070236Field001Chars00 ++ (fragment0070236Field002Chars00 ++ (fragment0070236Field003Chars00 ++ (fragment0070236Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 29)) hinput
    _ = SourceJson.object (fuel + 28) (SourceJson.white (fragment0070236Field000Chars00 ++ (fragment0070236Field001Chars00 ++ (fragment0070236Field002Chars00 ++ (fragment0070236Field003Chars00 ++ (fragment0070236Field004Chars00 ++ (tail))))))) fragment0070236Acc00000 := by rfl
    _ = SourceJson.object (fuel + 27) (SourceJson.white (fragment0070236Field001Chars00 ++ (fragment0070236Field002Chars00 ++ (fragment0070236Field003Chars00 ++ (fragment0070236Field004Chars00 ++ (tail)))))) fragment0070236Acc00100 := object_fragment0070236_field_000 fuel (fragment0070236Field001Chars00 ++ (fragment0070236Field002Chars00 ++ (fragment0070236Field003Chars00 ++ (fragment0070236Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 26) (SourceJson.white (fragment0070236Field002Chars00 ++ (fragment0070236Field003Chars00 ++ (fragment0070236Field004Chars00 ++ (tail))))) fragment0070236Acc00200 := object_fragment0070236_field_001 fuel (fragment0070236Field002Chars00 ++ (fragment0070236Field003Chars00 ++ (fragment0070236Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 25) (SourceJson.white (fragment0070236Field003Chars00 ++ (fragment0070236Field004Chars00 ++ (tail)))) fragment0070236Acc00300 := object_fragment0070236_field_002 fuel (fragment0070236Field003Chars00 ++ (fragment0070236Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 24) (SourceJson.white (fragment0070236Field004Chars00 ++ (tail))) fragment0070236Acc00400 := object_fragment0070236_field_003 fuel (fragment0070236Field004Chars00 ++ (tail))
    _ = .ok (fragment0070236Value, tail) := object_fragment0070236_field_004 fuel (tail)

noncomputable def fragment0072598Acc00000 : List SourceJson := []

noncomputable def fragment0072598Chunk000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0072598Chunk000Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3'])]) :: (acc))

theorem array_fragment0072598_chunk_000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 36) (SourceJson.white (fragment0072598Chunk000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 34) (SourceJson.white tail) (fragment0072598Chunk000Push00 acc) := by
  rfl

noncomputable def fragment0072598Acc00100 : List SourceJson := fragment0072598Chunk000Push00 fragment0072598Acc00000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0072598_array_chunk_000"
  err.flush

noncomputable def fragment0072598Chunk001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0072598Chunk001Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '7'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '7'])]) :: (acc))

theorem array_fragment0072598_chunk_001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 34) (SourceJson.white (fragment0072598Chunk001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 32) (SourceJson.white tail) (fragment0072598Chunk001Push00 acc) := by
  rfl

noncomputable def fragment0072598Acc00200 : List SourceJson := fragment0072598Chunk001Push00 fragment0072598Acc00100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0072598_array_chunk_001"
  err.flush

noncomputable def fragment0072598Chunk002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0072598Chunk002Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '7'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '7'])]) :: (acc))

theorem array_fragment0072598_chunk_002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 32) (SourceJson.white (fragment0072598Chunk002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 30) (SourceJson.white tail) (fragment0072598Chunk002Push00 acc) := by
  rfl

noncomputable def fragment0072598Acc00300 : List SourceJson := fragment0072598Chunk002Push00 fragment0072598Acc00200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0072598_array_chunk_002"
  err.flush

noncomputable def fragment0072598Chunk003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0072598Chunk003Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['6']), .number (String.ofList ['9']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '8']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '7'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '7'])]) :: (acc))

theorem array_fragment0072598_chunk_003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 30) (SourceJson.white (fragment0072598Chunk003Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 28) (SourceJson.white tail) (fragment0072598Chunk003Push00 acc) := by
  rfl

noncomputable def fragment0072598Acc00400 : List SourceJson := fragment0072598Chunk003Push00 fragment0072598Acc00300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0072598_array_chunk_003"
  err.flush

noncomputable def fragment0072598Chunk004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0072598Chunk004Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '7'])]) :: ((.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '6'])]) :: (acc))

theorem array_fragment0072598_chunk_004 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 28) (SourceJson.white (fragment0072598Chunk004Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 26) (SourceJson.white tail) (fragment0072598Chunk004Push00 acc) := by
  rfl

noncomputable def fragment0072598Acc00500 : List SourceJson := fragment0072598Chunk004Push00 fragment0072598Acc00400

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0072598_array_chunk_004"
  err.flush

noncomputable def fragment0072598Chunk005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']']
noncomputable def fragment0072598Chunk005Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '7'])]) :: (acc)

theorem array_fragment0072598_chunk_005 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 26) (SourceJson.white (fragment0072598Chunk005Chars00 ++ tail)) acc =
      .ok (.arr ((fragment0072598Chunk005Push00 acc).reverse), tail) := by
  rfl

noncomputable def fragment0072598Acc00600 : List SourceJson := fragment0072598Chunk005Push00 fragment0072598Acc00500

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0072598_array_chunk_005"
  err.flush

noncomputable def fragment0072598Chars : List Char := '[' :: (fragment0072598Chunk000Chars00 ++ fragment0072598Chunk001Chars00 ++ fragment0072598Chunk002Chars00 ++ fragment0072598Chunk003Chars00 ++ fragment0072598Chunk004Chars00 ++ fragment0072598Chunk005Chars00)
noncomputable def fragment0072598Value : SourceJson := .arr (fragment0072598Acc00600.reverse)

theorem value_fragment0072598 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 37) (fragment0072598Chars ++ tail) =
      .ok (fragment0072598Value, tail) := by
  have hinput : fragment0072598Chars ++ tail = '[' :: (fragment0072598Chunk000Chars00 ++ (fragment0072598Chunk001Chars00 ++ (fragment0072598Chunk002Chars00 ++ (fragment0072598Chunk003Chars00 ++ (fragment0072598Chunk004Chars00 ++ (fragment0072598Chunk005Chars00 ++ (tail))))))) := by
    simp only [fragment0072598Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 37) (fragment0072598Chars ++ tail) =
        SourceJson.value (fuel + 37) ('[' :: (fragment0072598Chunk000Chars00 ++ (fragment0072598Chunk001Chars00 ++ (fragment0072598Chunk002Chars00 ++ (fragment0072598Chunk003Chars00 ++ (fragment0072598Chunk004Chars00 ++ (fragment0072598Chunk005Chars00 ++ (tail)))))))) :=
      congrArg (SourceJson.value (fuel + 37)) hinput
    _ = SourceJson.array (fuel + 36) (SourceJson.white (fragment0072598Chunk000Chars00 ++ (fragment0072598Chunk001Chars00 ++ (fragment0072598Chunk002Chars00 ++ (fragment0072598Chunk003Chars00 ++ (fragment0072598Chunk004Chars00 ++ (fragment0072598Chunk005Chars00 ++ (tail)))))))) fragment0072598Acc00000 := by rfl
    _ = SourceJson.array (fuel + 34) (SourceJson.white (fragment0072598Chunk001Chars00 ++ (fragment0072598Chunk002Chars00 ++ (fragment0072598Chunk003Chars00 ++ (fragment0072598Chunk004Chars00 ++ (fragment0072598Chunk005Chars00 ++ (tail))))))) fragment0072598Acc00100 := array_fragment0072598_chunk_000 fuel (fragment0072598Chunk001Chars00 ++ (fragment0072598Chunk002Chars00 ++ (fragment0072598Chunk003Chars00 ++ (fragment0072598Chunk004Chars00 ++ (fragment0072598Chunk005Chars00 ++ (tail)))))) fragment0072598Acc00000
    _ = SourceJson.array (fuel + 32) (SourceJson.white (fragment0072598Chunk002Chars00 ++ (fragment0072598Chunk003Chars00 ++ (fragment0072598Chunk004Chars00 ++ (fragment0072598Chunk005Chars00 ++ (tail)))))) fragment0072598Acc00200 := array_fragment0072598_chunk_001 fuel (fragment0072598Chunk002Chars00 ++ (fragment0072598Chunk003Chars00 ++ (fragment0072598Chunk004Chars00 ++ (fragment0072598Chunk005Chars00 ++ (tail))))) fragment0072598Acc00100
    _ = SourceJson.array (fuel + 30) (SourceJson.white (fragment0072598Chunk003Chars00 ++ (fragment0072598Chunk004Chars00 ++ (fragment0072598Chunk005Chars00 ++ (tail))))) fragment0072598Acc00300 := array_fragment0072598_chunk_002 fuel (fragment0072598Chunk003Chars00 ++ (fragment0072598Chunk004Chars00 ++ (fragment0072598Chunk005Chars00 ++ (tail)))) fragment0072598Acc00200
    _ = SourceJson.array (fuel + 28) (SourceJson.white (fragment0072598Chunk004Chars00 ++ (fragment0072598Chunk005Chars00 ++ (tail)))) fragment0072598Acc00400 := array_fragment0072598_chunk_003 fuel (fragment0072598Chunk004Chars00 ++ (fragment0072598Chunk005Chars00 ++ (tail))) fragment0072598Acc00300
    _ = SourceJson.array (fuel + 26) (SourceJson.white (fragment0072598Chunk005Chars00 ++ (tail))) fragment0072598Acc00500 := array_fragment0072598_chunk_004 fuel (fragment0072598Chunk005Chars00 ++ (tail)) fragment0072598Acc00400
    _ = .ok (fragment0072598Value, tail) := array_fragment0072598_chunk_005 fuel (tail) fragment0072598Acc00500

noncomputable def fragment0072148Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0072148Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0072148Field000Value00 : SourceJson := .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '7'])]
noncomputable def fragment0072148Acc00100 : List (String × SourceJson) := (fragment0072148Field000Key00, fragment0072148Field000Value00) :: fragment0072148Acc00000
noncomputable def fragment0072148Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0072148_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 41) (SourceJson.white (fragment0072148Field000Chars00 ++ tail)) fragment0072148Acc00000 =
      SourceJson.object (fuel + 40) (SourceJson.white tail) fragment0072148Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0072148_object_field_000"
  err.flush

noncomputable def fragment0072148Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0072148Field001Value00 : SourceJson := .number (String.ofList ['8'])
noncomputable def fragment0072148Acc00200 : List (String × SourceJson) := (fragment0072148Field001Key00, fragment0072148Field001Value00) :: fragment0072148Acc00100
noncomputable def fragment0072148Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '8', ',']

theorem object_fragment0072148_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 40) (SourceJson.white (fragment0072148Field001Chars00 ++ tail)) fragment0072148Acc00100 =
      SourceJson.object (fuel + 39) (SourceJson.white tail) fragment0072148Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0072148_object_field_001"
  err.flush

noncomputable def fragment0072148Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0072148Field002Value00 : SourceJson := .number (String.ofList ['2', '7'])
noncomputable def fragment0072148Acc00300 : List (String × SourceJson) := (fragment0072148Field002Key00, fragment0072148Field002Value00) :: fragment0072148Acc00200
noncomputable def fragment0072148Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '2', '7', ',']

theorem object_fragment0072148_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 39) (SourceJson.white (fragment0072148Field002Chars00 ++ tail)) fragment0072148Acc00200 =
      SourceJson.object (fuel + 38) (SourceJson.white tail) fragment0072148Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0072148_object_field_002"
  err.flush

noncomputable def fragment0072148Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0072148Field003Value00 : SourceJson := fragment0072598Value
noncomputable def fragment0072148Acc00400 : List (String × SourceJson) := (fragment0072148Field003Key00, fragment0072148Field003Value00) :: fragment0072148Acc00300
noncomputable def fragment0072148Field003HeaderChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ']
noncomputable def fragment0072148Field003SuffixChars00 : List Char := [',']
noncomputable def fragment0072148Field003Chars00 : List Char := fragment0072148Field003HeaderChars00 ++ fragment0072598Chars ++ fragment0072148Field003SuffixChars00

noncomputable def fragment0072148Field003AfterValue00 (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending => .ok (.obj (((fragment0072148Field003Key00, result.1) :: fragment0072148Acc00300).reverse), ending)
  | ',' :: ending => SourceJson.object fuel (SourceJson.white ending) ((fragment0072148Field003Key00, result.1) :: fragment0072148Acc00300)
  | _ => .error "object separator missing"

theorem object_fragment0072148_field_003_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 38) (SourceJson.white (fragment0072148Field003HeaderChars00 ++ rest)) fragment0072148Acc00300 =
      (SourceJson.value (fuel + 37) rest).bind (fragment0072148Field003AfterValue00 (fuel + 37)) := by rfl

theorem object_fragment0072148_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 38) (SourceJson.white (fragment0072148Field003Chars00 ++ tail)) fragment0072148Acc00300 =
      SourceJson.object (fuel + 37) (SourceJson.white tail) fragment0072148Acc00400 := by
  have hinput : fragment0072148Field003Chars00 ++ tail = fragment0072148Field003HeaderChars00 ++ (fragment0072598Chars ++ (fragment0072148Field003SuffixChars00 ++ tail)) := by
    simp only [fragment0072148Field003Chars00, List.append_assoc]
  calc
    SourceJson.object (fuel + 38) (SourceJson.white (fragment0072148Field003Chars00 ++ tail)) fragment0072148Acc00300 =
        SourceJson.object (fuel + 38)
          (SourceJson.white (fragment0072148Field003HeaderChars00 ++ (fragment0072598Chars ++ (fragment0072148Field003SuffixChars00 ++ tail)))) fragment0072148Acc00300 :=
      congrArg (fun s => SourceJson.object (fuel + 38) (SourceJson.white s) fragment0072148Acc00300) hinput
    _ = (SourceJson.value (fuel + 37) (fragment0072598Chars ++ (fragment0072148Field003SuffixChars00 ++ tail))).bind
        (fragment0072148Field003AfterValue00 (fuel + 37)) := object_fragment0072148_field_003_header fuel (fragment0072598Chars ++ (fragment0072148Field003SuffixChars00 ++ tail))
    _ = (Except.ok (fragment0072598Value, fragment0072148Field003SuffixChars00 ++ tail)).bind (fragment0072148Field003AfterValue00 (fuel + 37)) :=
      congrArg (fun result => result.bind (fragment0072148Field003AfterValue00 (fuel + 37)))
        (value_fragment0072598 (fuel + 0) (fragment0072148Field003SuffixChars00 ++ tail))
    _ = SourceJson.object (fuel + 37) (SourceJson.white tail) fragment0072148Acc00400 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0072148_object_field_003"
  err.flush

noncomputable def fragment0072148Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0072148Field004Value00 : SourceJson := .number (String.ofList ['5', '6'])
noncomputable def fragment0072148Acc00500 : List (String × SourceJson) := (fragment0072148Field004Key00, fragment0072148Field004Value00) :: fragment0072148Acc00400
noncomputable def fragment0072148Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '5', '6', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0072148_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 37) (SourceJson.white (fragment0072148Field004Chars00 ++ tail)) fragment0072148Acc00400 =
      .ok (.obj (fragment0072148Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0072148_object_field_004"
  err.flush

noncomputable def fragment0072148Chars : List Char := '{' :: (fragment0072148Field000Chars00 ++ fragment0072148Field001Chars00 ++ fragment0072148Field002Chars00 ++ fragment0072148Field003Chars00 ++ fragment0072148Field004Chars00)
noncomputable def fragment0072148Value : SourceJson := .obj (fragment0072148Acc00500.reverse)

theorem value_fragment0072148 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 42) (fragment0072148Chars ++ tail) =
      .ok (fragment0072148Value, tail) := by
  have hinput : fragment0072148Chars ++ tail = '{' :: (fragment0072148Field000Chars00 ++ (fragment0072148Field001Chars00 ++ (fragment0072148Field002Chars00 ++ (fragment0072148Field003Chars00 ++ (fragment0072148Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0072148Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 42) (fragment0072148Chars ++ tail) =
        SourceJson.value (fuel + 42) ('{' :: (fragment0072148Field000Chars00 ++ (fragment0072148Field001Chars00 ++ (fragment0072148Field002Chars00 ++ (fragment0072148Field003Chars00 ++ (fragment0072148Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 42)) hinput
    _ = SourceJson.object (fuel + 41) (SourceJson.white (fragment0072148Field000Chars00 ++ (fragment0072148Field001Chars00 ++ (fragment0072148Field002Chars00 ++ (fragment0072148Field003Chars00 ++ (fragment0072148Field004Chars00 ++ (tail))))))) fragment0072148Acc00000 := by rfl
    _ = SourceJson.object (fuel + 40) (SourceJson.white (fragment0072148Field001Chars00 ++ (fragment0072148Field002Chars00 ++ (fragment0072148Field003Chars00 ++ (fragment0072148Field004Chars00 ++ (tail)))))) fragment0072148Acc00100 := object_fragment0072148_field_000 fuel (fragment0072148Field001Chars00 ++ (fragment0072148Field002Chars00 ++ (fragment0072148Field003Chars00 ++ (fragment0072148Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 39) (SourceJson.white (fragment0072148Field002Chars00 ++ (fragment0072148Field003Chars00 ++ (fragment0072148Field004Chars00 ++ (tail))))) fragment0072148Acc00200 := object_fragment0072148_field_001 fuel (fragment0072148Field002Chars00 ++ (fragment0072148Field003Chars00 ++ (fragment0072148Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 38) (SourceJson.white (fragment0072148Field003Chars00 ++ (fragment0072148Field004Chars00 ++ (tail)))) fragment0072148Acc00300 := object_fragment0072148_field_002 fuel (fragment0072148Field003Chars00 ++ (fragment0072148Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 37) (SourceJson.white (fragment0072148Field004Chars00 ++ (tail))) fragment0072148Acc00400 := object_fragment0072148_field_003 fuel (fragment0072148Field004Chars00 ++ (tail))
    _ = .ok (fragment0072148Value, tail) := object_fragment0072148_field_004 fuel (tail)

noncomputable def fragment0076565Acc00000 : List SourceJson := []

noncomputable def fragment0076565Chunk000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0076565Chunk000Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1'])]) :: (acc))

theorem array_fragment0076565_chunk_000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 31) (SourceJson.white (fragment0076565Chunk000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 29) (SourceJson.white tail) (fragment0076565Chunk000Push00 acc) := by
  rfl

noncomputable def fragment0076565Acc00100 : List SourceJson := fragment0076565Chunk000Push00 fragment0076565Acc00000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0076565_array_chunk_000"
  err.flush

noncomputable def fragment0076565Chunk001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0076565Chunk001Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3'])]) :: (acc))

theorem array_fragment0076565_chunk_001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 29) (SourceJson.white (fragment0076565Chunk001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 27) (SourceJson.white tail) (fragment0076565Chunk001Push00 acc) := by
  rfl

noncomputable def fragment0076565Acc00200 : List SourceJson := fragment0076565Chunk001Push00 fragment0076565Acc00100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0076565_array_chunk_001"
  err.flush

noncomputable def fragment0076565Chunk002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0076565Chunk002Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5'])]) :: (acc))

theorem array_fragment0076565_chunk_002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 27) (SourceJson.white (fragment0076565Chunk002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 25) (SourceJson.white tail) (fragment0076565Chunk002Push00 acc) := by
  rfl

noncomputable def fragment0076565Acc00300 : List SourceJson := fragment0076565Chunk002Push00 fragment0076565Acc00200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0076565_array_chunk_002"
  err.flush

noncomputable def fragment0076565Chunk003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0076565Chunk003Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['6']), .number (String.ofList ['9']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '8']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '5'])]) :: (acc))

theorem array_fragment0076565_chunk_003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 25) (SourceJson.white (fragment0076565Chunk003Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 23) (SourceJson.white tail) (fragment0076565Chunk003Push00 acc) := by
  rfl

noncomputable def fragment0076565Acc00400 : List SourceJson := fragment0076565Chunk003Push00 fragment0076565Acc00300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0076565_array_chunk_003"
  err.flush

noncomputable def fragment0076565Chunk004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']']
noncomputable def fragment0076565Chunk004Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5'])]) :: ((.arr [.number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5'])]) :: (acc))

theorem array_fragment0076565_chunk_004 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 23) (SourceJson.white (fragment0076565Chunk004Chars00 ++ tail)) acc =
      .ok (.arr ((fragment0076565Chunk004Push00 acc).reverse), tail) := by
  rfl

noncomputable def fragment0076565Acc00500 : List SourceJson := fragment0076565Chunk004Push00 fragment0076565Acc00400

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0076565_array_chunk_004"
  err.flush

noncomputable def fragment0076565Chars : List Char := '[' :: (fragment0076565Chunk000Chars00 ++ fragment0076565Chunk001Chars00 ++ fragment0076565Chunk002Chars00 ++ fragment0076565Chunk003Chars00 ++ fragment0076565Chunk004Chars00)
noncomputable def fragment0076565Value : SourceJson := .arr (fragment0076565Acc00500.reverse)

theorem value_fragment0076565 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 32) (fragment0076565Chars ++ tail) =
      .ok (fragment0076565Value, tail) := by
  have hinput : fragment0076565Chars ++ tail = '[' :: (fragment0076565Chunk000Chars00 ++ (fragment0076565Chunk001Chars00 ++ (fragment0076565Chunk002Chars00 ++ (fragment0076565Chunk003Chars00 ++ (fragment0076565Chunk004Chars00 ++ (tail)))))) := by
    simp only [fragment0076565Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 32) (fragment0076565Chars ++ tail) =
        SourceJson.value (fuel + 32) ('[' :: (fragment0076565Chunk000Chars00 ++ (fragment0076565Chunk001Chars00 ++ (fragment0076565Chunk002Chars00 ++ (fragment0076565Chunk003Chars00 ++ (fragment0076565Chunk004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 32)) hinput
    _ = SourceJson.array (fuel + 31) (SourceJson.white (fragment0076565Chunk000Chars00 ++ (fragment0076565Chunk001Chars00 ++ (fragment0076565Chunk002Chars00 ++ (fragment0076565Chunk003Chars00 ++ (fragment0076565Chunk004Chars00 ++ (tail))))))) fragment0076565Acc00000 := by rfl
    _ = SourceJson.array (fuel + 29) (SourceJson.white (fragment0076565Chunk001Chars00 ++ (fragment0076565Chunk002Chars00 ++ (fragment0076565Chunk003Chars00 ++ (fragment0076565Chunk004Chars00 ++ (tail)))))) fragment0076565Acc00100 := array_fragment0076565_chunk_000 fuel (fragment0076565Chunk001Chars00 ++ (fragment0076565Chunk002Chars00 ++ (fragment0076565Chunk003Chars00 ++ (fragment0076565Chunk004Chars00 ++ (tail))))) fragment0076565Acc00000
    _ = SourceJson.array (fuel + 27) (SourceJson.white (fragment0076565Chunk002Chars00 ++ (fragment0076565Chunk003Chars00 ++ (fragment0076565Chunk004Chars00 ++ (tail))))) fragment0076565Acc00200 := array_fragment0076565_chunk_001 fuel (fragment0076565Chunk002Chars00 ++ (fragment0076565Chunk003Chars00 ++ (fragment0076565Chunk004Chars00 ++ (tail)))) fragment0076565Acc00100
    _ = SourceJson.array (fuel + 25) (SourceJson.white (fragment0076565Chunk003Chars00 ++ (fragment0076565Chunk004Chars00 ++ (tail)))) fragment0076565Acc00300 := array_fragment0076565_chunk_002 fuel (fragment0076565Chunk003Chars00 ++ (fragment0076565Chunk004Chars00 ++ (tail))) fragment0076565Acc00200
    _ = SourceJson.array (fuel + 23) (SourceJson.white (fragment0076565Chunk004Chars00 ++ (tail))) fragment0076565Acc00400 := array_fragment0076565_chunk_003 fuel (fragment0076565Chunk004Chars00 ++ (tail)) fragment0076565Acc00300
    _ = .ok (fragment0076565Value, tail) := array_fragment0076565_chunk_004 fuel (tail) fragment0076565Acc00400

noncomputable def fragment0076167Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0076167Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0076167Field000Value00 : SourceJson := .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5'])]
noncomputable def fragment0076167Acc00100 : List (String × SourceJson) := (fragment0076167Field000Key00, fragment0076167Field000Value00) :: fragment0076167Acc00000
noncomputable def fragment0076167Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0076167_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 36) (SourceJson.white (fragment0076167Field000Chars00 ++ tail)) fragment0076167Acc00000 =
      SourceJson.object (fuel + 35) (SourceJson.white tail) fragment0076167Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0076167_object_field_000"
  err.flush

noncomputable def fragment0076167Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0076167Field001Value00 : SourceJson := .number (String.ofList ['7'])
noncomputable def fragment0076167Acc00200 : List (String × SourceJson) := (fragment0076167Field001Key00, fragment0076167Field001Value00) :: fragment0076167Acc00100
noncomputable def fragment0076167Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '7', ',']

theorem object_fragment0076167_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 35) (SourceJson.white (fragment0076167Field001Chars00 ++ tail)) fragment0076167Acc00100 =
      SourceJson.object (fuel + 34) (SourceJson.white tail) fragment0076167Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0076167_object_field_001"
  err.flush

noncomputable def fragment0076167Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0076167Field002Value00 : SourceJson := .number (String.ofList ['2', '5'])
noncomputable def fragment0076167Acc00300 : List (String × SourceJson) := (fragment0076167Field002Key00, fragment0076167Field002Value00) :: fragment0076167Acc00200
noncomputable def fragment0076167Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '2', '5', ',']

theorem object_fragment0076167_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 34) (SourceJson.white (fragment0076167Field002Chars00 ++ tail)) fragment0076167Acc00200 =
      SourceJson.object (fuel + 33) (SourceJson.white tail) fragment0076167Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0076167_object_field_002"
  err.flush

noncomputable def fragment0076167Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0076167Field003Value00 : SourceJson := fragment0076565Value
noncomputable def fragment0076167Acc00400 : List (String × SourceJson) := (fragment0076167Field003Key00, fragment0076167Field003Value00) :: fragment0076167Acc00300
noncomputable def fragment0076167Field003HeaderChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ']
noncomputable def fragment0076167Field003SuffixChars00 : List Char := [',']
noncomputable def fragment0076167Field003Chars00 : List Char := fragment0076167Field003HeaderChars00 ++ fragment0076565Chars ++ fragment0076167Field003SuffixChars00

noncomputable def fragment0076167Field003AfterValue00 (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending => .ok (.obj (((fragment0076167Field003Key00, result.1) :: fragment0076167Acc00300).reverse), ending)
  | ',' :: ending => SourceJson.object fuel (SourceJson.white ending) ((fragment0076167Field003Key00, result.1) :: fragment0076167Acc00300)
  | _ => .error "object separator missing"

theorem object_fragment0076167_field_003_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 33) (SourceJson.white (fragment0076167Field003HeaderChars00 ++ rest)) fragment0076167Acc00300 =
      (SourceJson.value (fuel + 32) rest).bind (fragment0076167Field003AfterValue00 (fuel + 32)) := by rfl

theorem object_fragment0076167_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 33) (SourceJson.white (fragment0076167Field003Chars00 ++ tail)) fragment0076167Acc00300 =
      SourceJson.object (fuel + 32) (SourceJson.white tail) fragment0076167Acc00400 := by
  have hinput : fragment0076167Field003Chars00 ++ tail = fragment0076167Field003HeaderChars00 ++ (fragment0076565Chars ++ (fragment0076167Field003SuffixChars00 ++ tail)) := by
    simp only [fragment0076167Field003Chars00, List.append_assoc]
  calc
    SourceJson.object (fuel + 33) (SourceJson.white (fragment0076167Field003Chars00 ++ tail)) fragment0076167Acc00300 =
        SourceJson.object (fuel + 33)
          (SourceJson.white (fragment0076167Field003HeaderChars00 ++ (fragment0076565Chars ++ (fragment0076167Field003SuffixChars00 ++ tail)))) fragment0076167Acc00300 :=
      congrArg (fun s => SourceJson.object (fuel + 33) (SourceJson.white s) fragment0076167Acc00300) hinput
    _ = (SourceJson.value (fuel + 32) (fragment0076565Chars ++ (fragment0076167Field003SuffixChars00 ++ tail))).bind
        (fragment0076167Field003AfterValue00 (fuel + 32)) := object_fragment0076167_field_003_header fuel (fragment0076565Chars ++ (fragment0076167Field003SuffixChars00 ++ tail))
    _ = (Except.ok (fragment0076565Value, fragment0076167Field003SuffixChars00 ++ tail)).bind (fragment0076167Field003AfterValue00 (fuel + 32)) :=
      congrArg (fun result => result.bind (fragment0076167Field003AfterValue00 (fuel + 32)))
        (value_fragment0076565 (fuel + 0) (fragment0076167Field003SuffixChars00 ++ tail))
    _ = SourceJson.object (fuel + 32) (SourceJson.white tail) fragment0076167Acc00400 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0076167_object_field_003"
  err.flush

noncomputable def fragment0076167Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0076167Field004Value00 : SourceJson := .number (String.ofList ['4', '2'])
noncomputable def fragment0076167Acc00500 : List (String × SourceJson) := (fragment0076167Field004Key00, fragment0076167Field004Value00) :: fragment0076167Acc00400
noncomputable def fragment0076167Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '4', '2', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0076167_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 32) (SourceJson.white (fragment0076167Field004Chars00 ++ tail)) fragment0076167Acc00400 =
      .ok (.obj (fragment0076167Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0076167_object_field_004"
  err.flush

noncomputable def fragment0076167Chars : List Char := '{' :: (fragment0076167Field000Chars00 ++ fragment0076167Field001Chars00 ++ fragment0076167Field002Chars00 ++ fragment0076167Field003Chars00 ++ fragment0076167Field004Chars00)
noncomputable def fragment0076167Value : SourceJson := .obj (fragment0076167Acc00500.reverse)

theorem value_fragment0076167 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 37) (fragment0076167Chars ++ tail) =
      .ok (fragment0076167Value, tail) := by
  have hinput : fragment0076167Chars ++ tail = '{' :: (fragment0076167Field000Chars00 ++ (fragment0076167Field001Chars00 ++ (fragment0076167Field002Chars00 ++ (fragment0076167Field003Chars00 ++ (fragment0076167Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0076167Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 37) (fragment0076167Chars ++ tail) =
        SourceJson.value (fuel + 37) ('{' :: (fragment0076167Field000Chars00 ++ (fragment0076167Field001Chars00 ++ (fragment0076167Field002Chars00 ++ (fragment0076167Field003Chars00 ++ (fragment0076167Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 37)) hinput
    _ = SourceJson.object (fuel + 36) (SourceJson.white (fragment0076167Field000Chars00 ++ (fragment0076167Field001Chars00 ++ (fragment0076167Field002Chars00 ++ (fragment0076167Field003Chars00 ++ (fragment0076167Field004Chars00 ++ (tail))))))) fragment0076167Acc00000 := by rfl
    _ = SourceJson.object (fuel + 35) (SourceJson.white (fragment0076167Field001Chars00 ++ (fragment0076167Field002Chars00 ++ (fragment0076167Field003Chars00 ++ (fragment0076167Field004Chars00 ++ (tail)))))) fragment0076167Acc00100 := object_fragment0076167_field_000 fuel (fragment0076167Field001Chars00 ++ (fragment0076167Field002Chars00 ++ (fragment0076167Field003Chars00 ++ (fragment0076167Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 34) (SourceJson.white (fragment0076167Field002Chars00 ++ (fragment0076167Field003Chars00 ++ (fragment0076167Field004Chars00 ++ (tail))))) fragment0076167Acc00200 := object_fragment0076167_field_001 fuel (fragment0076167Field002Chars00 ++ (fragment0076167Field003Chars00 ++ (fragment0076167Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 33) (SourceJson.white (fragment0076167Field003Chars00 ++ (fragment0076167Field004Chars00 ++ (tail)))) fragment0076167Acc00300 := object_fragment0076167_field_002 fuel (fragment0076167Field003Chars00 ++ (fragment0076167Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 32) (SourceJson.white (fragment0076167Field004Chars00 ++ (tail))) fragment0076167Acc00400 := object_fragment0076167_field_003 fuel (fragment0076167Field004Chars00 ++ (tail))
    _ = .ok (fragment0076167Value, tail) := object_fragment0076167_field_004 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0000_before_reader"
  err.flush

noncomputable def chunk0000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '2', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0000Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['2'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['3'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['0']), .number (String.ofList ['1'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['2'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['3'])], .arr [.number (String.ofList ['2']), .number (String.ofList ['3'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['2']))]) :: ((.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['0']), .number (String.ofList ['1'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['1'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['1'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['0'])], .arr [.number (String.ofList ['1'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['1']))]) :: (acc))

theorem array_chunk0000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 61) (SourceJson.white (chunk0000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 59) (SourceJson.white tail) (chunk0000Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0000_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0001_before_reader"
  err.flush

noncomputable def chunk0001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '3', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0001Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['3'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['5'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['4']), .number (String.ofList ['5'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['4'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5'])], .arr [.number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['3']))]) :: (acc)

theorem array_chunk0001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 59) (SourceJson.white (chunk0001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 58) (SourceJson.white tail) (chunk0001Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0001_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0002_before_reader"
  err.flush

noncomputable def chunk0002LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0002SuffixChars00 : List Char := [',']
noncomputable def chunk0002Chars00 : List Char := chunk0002LeadChars00 ++ fragment0066820Chars ++ chunk0002SuffixChars00
noncomputable def chunk0002Push00 (acc : List SourceJson) : List SourceJson := fragment0066820Value :: acc

noncomputable def chunk0002AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0002_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 58)
      (SourceJson.white (chunk0002LeadChars00 ++ (fragment0066820Chars ++ rest))) acc =
      (SourceJson.value (fuel + 57) (fragment0066820Chars ++ rest)).bind
        (chunk0002AfterValue00 (fuel + 57) acc) := by rfl

theorem array_chunk0002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 58) (SourceJson.white (chunk0002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 57) (SourceJson.white tail) (chunk0002Push00 acc) := by
  have hinput : chunk0002Chars00 ++ tail = chunk0002LeadChars00 ++ (fragment0066820Chars ++ (chunk0002SuffixChars00 ++ tail)) := by
    simp only [chunk0002Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 58) (SourceJson.white (chunk0002Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 58)
          (SourceJson.white (chunk0002LeadChars00 ++ (fragment0066820Chars ++ (chunk0002SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 58) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 57) (fragment0066820Chars ++ (chunk0002SuffixChars00 ++ tail))).bind
        (chunk0002AfterValue00 (fuel + 57) acc) := array_chunk0002_head fuel (chunk0002SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0066820Value, chunk0002SuffixChars00 ++ tail)).bind
        (chunk0002AfterValue00 (fuel + 57) acc) :=
      congrArg (fun result => result.bind (chunk0002AfterValue00 (fuel + 57) acc))
        (value_fragment0066820 (fuel + 37) (chunk0002SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 57) (SourceJson.white tail) (chunk0002Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0002_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0003_before_reader"
  err.flush

noncomputable def chunk0003LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0003SuffixChars00 : List Char := [',']
noncomputable def chunk0003Chars00 : List Char := chunk0003LeadChars00 ++ fragment0067637Chars ++ chunk0003SuffixChars00
noncomputable def chunk0003Push00 (acc : List SourceJson) : List SourceJson := fragment0067637Value :: acc

noncomputable def chunk0003AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0003_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 57)
      (SourceJson.white (chunk0003LeadChars00 ++ (fragment0067637Chars ++ rest))) acc =
      (SourceJson.value (fuel + 56) (fragment0067637Chars ++ rest)).bind
        (chunk0003AfterValue00 (fuel + 56) acc) := by rfl

theorem array_chunk0003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 57) (SourceJson.white (chunk0003Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 56) (SourceJson.white tail) (chunk0003Push00 acc) := by
  have hinput : chunk0003Chars00 ++ tail = chunk0003LeadChars00 ++ (fragment0067637Chars ++ (chunk0003SuffixChars00 ++ tail)) := by
    simp only [chunk0003Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 57) (SourceJson.white (chunk0003Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 57)
          (SourceJson.white (chunk0003LeadChars00 ++ (fragment0067637Chars ++ (chunk0003SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 57) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 56) (fragment0067637Chars ++ (chunk0003SuffixChars00 ++ tail))).bind
        (chunk0003AfterValue00 (fuel + 56) acc) := array_chunk0003_head fuel (chunk0003SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0067637Value, chunk0003SuffixChars00 ++ tail)).bind
        (chunk0003AfterValue00 (fuel + 56) acc) :=
      congrArg (fun result => result.bind (chunk0003AfterValue00 (fuel + 56) acc))
        (value_fragment0067637 (fuel + 33) (chunk0003SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 56) (SourceJson.white tail) (chunk0003Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0003_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0004_before_reader"
  err.flush

noncomputable def chunk0004LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0004SuffixChars00 : List Char := [',']
noncomputable def chunk0004Chars00 : List Char := chunk0004LeadChars00 ++ fragment0068752Chars ++ chunk0004SuffixChars00
noncomputable def chunk0004Push00 (acc : List SourceJson) : List SourceJson := fragment0068752Value :: acc

noncomputable def chunk0004AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0004_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 56)
      (SourceJson.white (chunk0004LeadChars00 ++ (fragment0068752Chars ++ rest))) acc =
      (SourceJson.value (fuel + 55) (fragment0068752Chars ++ rest)).bind
        (chunk0004AfterValue00 (fuel + 55) acc) := by rfl

theorem array_chunk0004 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 56) (SourceJson.white (chunk0004Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 55) (SourceJson.white tail) (chunk0004Push00 acc) := by
  have hinput : chunk0004Chars00 ++ tail = chunk0004LeadChars00 ++ (fragment0068752Chars ++ (chunk0004SuffixChars00 ++ tail)) := by
    simp only [chunk0004Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 56) (SourceJson.white (chunk0004Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 56)
          (SourceJson.white (chunk0004LeadChars00 ++ (fragment0068752Chars ++ (chunk0004SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 56) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 55) (fragment0068752Chars ++ (chunk0004SuffixChars00 ++ tail))).bind
        (chunk0004AfterValue00 (fuel + 55) acc) := array_chunk0004_head fuel (chunk0004SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0068752Value, chunk0004SuffixChars00 ++ tail)).bind
        (chunk0004AfterValue00 (fuel + 55) acc) :=
      congrArg (fun result => result.bind (chunk0004AfterValue00 (fuel + 55) acc))
        (value_fragment0068752 (fuel + 29) (chunk0004SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 55) (SourceJson.white tail) (chunk0004Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0004_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0005_before_reader"
  err.flush

noncomputable def chunk0005LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0005SuffixChars00 : List Char := [',']
noncomputable def chunk0005Chars00 : List Char := chunk0005LeadChars00 ++ fragment0070236Chars ++ chunk0005SuffixChars00
noncomputable def chunk0005Push00 (acc : List SourceJson) : List SourceJson := fragment0070236Value :: acc

noncomputable def chunk0005AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0005_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 55)
      (SourceJson.white (chunk0005LeadChars00 ++ (fragment0070236Chars ++ rest))) acc =
      (SourceJson.value (fuel + 54) (fragment0070236Chars ++ rest)).bind
        (chunk0005AfterValue00 (fuel + 54) acc) := by rfl

theorem array_chunk0005 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 55) (SourceJson.white (chunk0005Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 54) (SourceJson.white tail) (chunk0005Push00 acc) := by
  have hinput : chunk0005Chars00 ++ tail = chunk0005LeadChars00 ++ (fragment0070236Chars ++ (chunk0005SuffixChars00 ++ tail)) := by
    simp only [chunk0005Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 55) (SourceJson.white (chunk0005Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 55)
          (SourceJson.white (chunk0005LeadChars00 ++ (fragment0070236Chars ++ (chunk0005SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 55) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 54) (fragment0070236Chars ++ (chunk0005SuffixChars00 ++ tail))).bind
        (chunk0005AfterValue00 (fuel + 54) acc) := array_chunk0005_head fuel (chunk0005SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0070236Value, chunk0005SuffixChars00 ++ tail)).bind
        (chunk0005AfterValue00 (fuel + 54) acc) :=
      congrArg (fun result => result.bind (chunk0005AfterValue00 (fuel + 54) acc))
        (value_fragment0070236 (fuel + 25) (chunk0005SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 54) (SourceJson.white tail) (chunk0005Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0005_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0006_before_reader"
  err.flush

noncomputable def chunk0006LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0006SuffixChars00 : List Char := [',']
noncomputable def chunk0006Chars00 : List Char := chunk0006LeadChars00 ++ fragment0072148Chars ++ chunk0006SuffixChars00
noncomputable def chunk0006Push00 (acc : List SourceJson) : List SourceJson := fragment0072148Value :: acc

noncomputable def chunk0006AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0006_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 54)
      (SourceJson.white (chunk0006LeadChars00 ++ (fragment0072148Chars ++ rest))) acc =
      (SourceJson.value (fuel + 53) (fragment0072148Chars ++ rest)).bind
        (chunk0006AfterValue00 (fuel + 53) acc) := by rfl

theorem array_chunk0006 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 54) (SourceJson.white (chunk0006Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 53) (SourceJson.white tail) (chunk0006Push00 acc) := by
  have hinput : chunk0006Chars00 ++ tail = chunk0006LeadChars00 ++ (fragment0072148Chars ++ (chunk0006SuffixChars00 ++ tail)) := by
    simp only [chunk0006Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 54) (SourceJson.white (chunk0006Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 54)
          (SourceJson.white (chunk0006LeadChars00 ++ (fragment0072148Chars ++ (chunk0006SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 54) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 53) (fragment0072148Chars ++ (chunk0006SuffixChars00 ++ tail))).bind
        (chunk0006AfterValue00 (fuel + 53) acc) := array_chunk0006_head fuel (chunk0006SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0072148Value, chunk0006SuffixChars00 ++ tail)).bind
        (chunk0006AfterValue00 (fuel + 53) acc) :=
      congrArg (fun result => result.bind (chunk0006AfterValue00 (fuel + 53) acc))
        (value_fragment0072148 (fuel + 11) (chunk0006SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 53) (SourceJson.white tail) (chunk0006Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0006_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0007_before_reader"
  err.flush

noncomputable def chunk0007LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0007SuffixChars00 : List Char := [',']
noncomputable def chunk0007Chars00 : List Char := chunk0007LeadChars00 ++ fragment0076167Chars ++ chunk0007SuffixChars00
noncomputable def chunk0007Push00 (acc : List SourceJson) : List SourceJson := fragment0076167Value :: acc

noncomputable def chunk0007AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0007_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 53)
      (SourceJson.white (chunk0007LeadChars00 ++ (fragment0076167Chars ++ rest))) acc =
      (SourceJson.value (fuel + 52) (fragment0076167Chars ++ rest)).bind
        (chunk0007AfterValue00 (fuel + 52) acc) := by rfl

theorem array_chunk0007 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 53) (SourceJson.white (chunk0007Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 52) (SourceJson.white tail) (chunk0007Push00 acc) := by
  have hinput : chunk0007Chars00 ++ tail = chunk0007LeadChars00 ++ (fragment0076167Chars ++ (chunk0007SuffixChars00 ++ tail)) := by
    simp only [chunk0007Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 53) (SourceJson.white (chunk0007Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 53)
          (SourceJson.white (chunk0007LeadChars00 ++ (fragment0076167Chars ++ (chunk0007SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 53) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 52) (fragment0076167Chars ++ (chunk0007SuffixChars00 ++ tail))).bind
        (chunk0007AfterValue00 (fuel + 52) acc) := array_chunk0007_head fuel (chunk0007SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0076167Value, chunk0007SuffixChars00 ++ tail)).bind
        (chunk0007AfterValue00 (fuel + 52) acc) :=
      congrArg (fun result => result.bind (chunk0007AfterValue00 (fuel + 52) acc))
        (value_fragment0076167 (fuel + 15) (chunk0007SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 52) (SourceJson.white tail) (chunk0007Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0007_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0000Chars00 ++ chunk0001Chars00 ++ chunk0002Chars00 ++ chunk0003Chars00 ++ chunk0004Chars00 ++ chunk0005Chars00 ++ chunk0006Chars00 ++ chunk0007Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0007Push00 (chunk0006Push00 (chunk0005Push00 (chunk0004Push00 (chunk0003Push00 (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc))))))))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 61) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 52) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0000Chars00 ++ (chunk0001Chars00 ++ (chunk0002Chars00 ++ (chunk0003Chars00 ++ (chunk0004Chars00 ++ (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail)))))))) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 61) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 61) (SourceJson.white (chunk0000Chars00 ++ (chunk0001Chars00 ++ (chunk0002Chars00 ++ (chunk0003Chars00 ++ (chunk0004Chars00 ++ (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail)))))))))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 61) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 59) (SourceJson.white (chunk0001Chars00 ++ (chunk0002Chars00 ++ (chunk0003Chars00 ++ (chunk0004Chars00 ++ (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail))))))))) (chunk0000Push00 (acc)) := array_chunk0000 fuel (chunk0001Chars00 ++ (chunk0002Chars00 ++ (chunk0003Chars00 ++ (chunk0004Chars00 ++ (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail)))))))) (acc)
    _ = SourceJson.array (fuel + 58) (SourceJson.white (chunk0002Chars00 ++ (chunk0003Chars00 ++ (chunk0004Chars00 ++ (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail)))))))) (chunk0001Push00 (chunk0000Push00 (acc))) := array_chunk0001 fuel (chunk0002Chars00 ++ (chunk0003Chars00 ++ (chunk0004Chars00 ++ (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail))))))) (chunk0000Push00 (acc))
    _ = SourceJson.array (fuel + 57) (SourceJson.white (chunk0003Chars00 ++ (chunk0004Chars00 ++ (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail))))))) (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc)))) := array_chunk0002 fuel (chunk0003Chars00 ++ (chunk0004Chars00 ++ (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail)))))) (chunk0001Push00 (chunk0000Push00 (acc)))
    _ = SourceJson.array (fuel + 56) (SourceJson.white (chunk0004Chars00 ++ (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail)))))) (chunk0003Push00 (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc))))) := array_chunk0003 fuel (chunk0004Chars00 ++ (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail))))) (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc))))
    _ = SourceJson.array (fuel + 55) (SourceJson.white (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail))))) (chunk0004Push00 (chunk0003Push00 (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc)))))) := array_chunk0004 fuel (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail)))) (chunk0003Push00 (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc)))))
    _ = SourceJson.array (fuel + 54) (SourceJson.white (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail)))) (chunk0005Push00 (chunk0004Push00 (chunk0003Push00 (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc))))))) := array_chunk0005 fuel (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail))) (chunk0004Push00 (chunk0003Push00 (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc))))))
    _ = SourceJson.array (fuel + 53) (SourceJson.white (chunk0007Chars00 ++ (tail))) (chunk0006Push00 (chunk0005Push00 (chunk0004Push00 (chunk0003Push00 (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc)))))))) := array_chunk0006 fuel (chunk0007Chars00 ++ (tail)) (chunk0005Push00 (chunk0004Push00 (chunk0003Push00 (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc)))))))
    _ = SourceJson.array (fuel + 52) (SourceJson.white tail) (blockPush acc) := array_chunk0007 fuel (tail) (chunk0006Push00 (chunk0005Push00 (chunk0004Push00 (chunk0003Push00 (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc))))))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 65613).take 13663 = blockChars := by rfl

theorem block_original_split : sourceRest 65613 = blockChars ++ sourceRest 79276 := by
  calc
    sourceRest 65613 = (sourceRest 65613).take 13663 ++ (sourceRest 65613).drop 13663 :=
      (List.take_append_drop 13663 (sourceRest 65613)).symm
    _ = blockChars ++ (sourceRest 65613).drop 13663 :=
      congrArg (fun part => part ++ (sourceRest 65613).drop 13663) block_original_prefix
    _ = blockChars ++ sourceRest 79276 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 65613 13663)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 61) (SourceJson.white (sourceRest 65613)) acc =
      SourceJson.array (fuel + 52) (SourceJson.white (sourceRest 79276)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 61) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 79276) acc)

#print axioms object_fragment0066820_field_000
#print axioms object_fragment0066820_field_001
#print axioms object_fragment0066820_field_002
#print axioms object_fragment0066820_field_003
#print axioms object_fragment0066820_field_004
#print axioms value_fragment0066820
#print axioms array_fragment0067852_chunk_000
#print axioms array_fragment0067852_chunk_001
#print axioms array_fragment0067852_chunk_002
#print axioms array_fragment0067852_chunk_003
#print axioms value_fragment0067852
#print axioms object_fragment0067637_field_000
#print axioms object_fragment0067637_field_001
#print axioms object_fragment0067637_field_002
#print axioms object_fragment0067637_field_003_header
#print axioms object_fragment0067637_field_003
#print axioms object_fragment0067637_field_004
#print axioms value_fragment0067637
#print axioms array_fragment0068994_chunk_000
#print axioms array_fragment0068994_chunk_001
#print axioms array_fragment0068994_chunk_002
#print axioms array_fragment0068994_chunk_003
#print axioms value_fragment0068994
#print axioms object_fragment0068752_field_000
#print axioms object_fragment0068752_field_001
#print axioms object_fragment0068752_field_002
#print axioms object_fragment0068752_field_003_header
#print axioms object_fragment0068752_field_003
#print axioms object_fragment0068752_field_004
#print axioms value_fragment0068752
#print axioms array_fragment0070504_chunk_000
#print axioms array_fragment0070504_chunk_001
#print axioms array_fragment0070504_chunk_002
#print axioms array_fragment0070504_chunk_003
#print axioms array_fragment0070504_chunk_004
#print axioms value_fragment0070504
#print axioms object_fragment0070236_field_000
#print axioms object_fragment0070236_field_001
#print axioms object_fragment0070236_field_002
#print axioms object_fragment0070236_field_003_header
#print axioms object_fragment0070236_field_003
#print axioms object_fragment0070236_field_004
#print axioms value_fragment0070236
#print axioms array_fragment0072598_chunk_000
#print axioms array_fragment0072598_chunk_001
#print axioms array_fragment0072598_chunk_002
#print axioms array_fragment0072598_chunk_003
#print axioms array_fragment0072598_chunk_004
#print axioms array_fragment0072598_chunk_005
#print axioms value_fragment0072598
#print axioms object_fragment0072148_field_000
#print axioms object_fragment0072148_field_001
#print axioms object_fragment0072148_field_002
#print axioms object_fragment0072148_field_003_header
#print axioms object_fragment0072148_field_003
#print axioms object_fragment0072148_field_004
#print axioms value_fragment0072148
#print axioms array_fragment0076565_chunk_000
#print axioms array_fragment0076565_chunk_001
#print axioms array_fragment0076565_chunk_002
#print axioms array_fragment0076565_chunk_003
#print axioms array_fragment0076565_chunk_004
#print axioms value_fragment0076565
#print axioms object_fragment0076167_field_000
#print axioms object_fragment0076167_field_001
#print axioms object_fragment0076167_field_002
#print axioms object_fragment0076167_field_003_header
#print axioms object_fragment0076167_field_003
#print axioms object_fragment0076167_field_004
#print axioms value_fragment0076167
#print axioms array_chunk0000
#print axioms array_chunk0001
#print axioms array_chunk0002_head
#print axioms array_chunk0002
#print axioms array_chunk0003_head
#print axioms array_chunk0003
#print axioms array_chunk0004_head
#print axioms array_chunk0004
#print axioms array_chunk0005_head
#print axioms array_chunk0005
#print axioms array_chunk0006_head
#print axioms array_chunk0006
#print axioms array_chunk0007_head
#print axioms array_chunk0007
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end FaceLedgerBlock000

end ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
