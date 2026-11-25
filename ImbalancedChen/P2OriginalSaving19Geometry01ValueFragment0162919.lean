import ImbalancedChen.P2OriginalSaving19Geometry01DirectInput
import ImbalancedChen.P2OriginalSaving19Geometry01ValueFragment0163447

/-! Original self-delimiting child; structured readers use separately checked child certificates.
Original-reader equations and exact production packed-input slices are checked
in Lean. No whole-cell parse or typed decoding claim is made by this pilot. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

noncomputable def fragment0162919Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0162919Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0162919Field000Value00 : SourceJson := .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '7']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '9']), .number (String.ofList ['3', '2']), .number (String.ofList ['3', '3']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '5'])]
noncomputable def fragment0162919Acc00100 : List (String × SourceJson) := (fragment0162919Field000Key00, fragment0162919Field000Value00) :: fragment0162919Acc00000
noncomputable def fragment0162919Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0162919_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 44) (SourceJson.white (fragment0162919Field000Chars00 ++ tail)) fragment0162919Acc00000 =
      SourceJson.object (fuel + 43) (SourceJson.white tail) fragment0162919Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0162919_object_field_000"
  err.flush

noncomputable def fragment0162919Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0162919Field001Value00 : SourceJson := .number (String.ofList ['7'])
noncomputable def fragment0162919Acc00200 : List (String × SourceJson) := (fragment0162919Field001Key00, fragment0162919Field001Value00) :: fragment0162919Acc00100
noncomputable def fragment0162919Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '7', ',']

theorem object_fragment0162919_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 43) (SourceJson.white (fragment0162919Field001Chars00 ++ tail)) fragment0162919Acc00100 =
      SourceJson.object (fuel + 42) (SourceJson.white tail) fragment0162919Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0162919_object_field_001"
  err.flush

noncomputable def fragment0162919Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0162919Field002Value00 : SourceJson := .number (String.ofList ['3', '5'])
noncomputable def fragment0162919Acc00300 : List (String × SourceJson) := (fragment0162919Field002Key00, fragment0162919Field002Value00) :: fragment0162919Acc00200
noncomputable def fragment0162919Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '3', '5', ',']

theorem object_fragment0162919_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 42) (SourceJson.white (fragment0162919Field002Chars00 ++ tail)) fragment0162919Acc00200 =
      SourceJson.object (fuel + 41) (SourceJson.white tail) fragment0162919Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0162919_object_field_002"
  err.flush

noncomputable def fragment0162919Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0162919Field003Value00 : SourceJson := fragment0163447Value
noncomputable def fragment0162919Acc00400 : List (String × SourceJson) := (fragment0162919Field003Key00, fragment0162919Field003Value00) :: fragment0162919Acc00300
noncomputable def fragment0162919Field003HeaderChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ']
noncomputable def fragment0162919Field003SuffixChars00 : List Char := [',']
noncomputable def fragment0162919Field003Chars00 : List Char := fragment0162919Field003HeaderChars00 ++ fragment0163447Chars ++ fragment0162919Field003SuffixChars00

noncomputable def fragment0162919Field003AfterValue00 (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending => .ok (.obj (((fragment0162919Field003Key00, result.1) :: fragment0162919Acc00300).reverse), ending)
  | ',' :: ending => SourceJson.object fuel (SourceJson.white ending) ((fragment0162919Field003Key00, result.1) :: fragment0162919Acc00300)
  | _ => .error "object separator missing"

theorem object_fragment0162919_field_003_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 41) (SourceJson.white (fragment0162919Field003HeaderChars00 ++ rest)) fragment0162919Acc00300 =
      (SourceJson.value (fuel + 40) rest).bind (fragment0162919Field003AfterValue00 (fuel + 40)) := by rfl

theorem object_fragment0162919_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 41) (SourceJson.white (fragment0162919Field003Chars00 ++ tail)) fragment0162919Acc00300 =
      SourceJson.object (fuel + 40) (SourceJson.white tail) fragment0162919Acc00400 := by
  have hinput : fragment0162919Field003Chars00 ++ tail = fragment0162919Field003HeaderChars00 ++ (fragment0163447Chars ++ (fragment0162919Field003SuffixChars00 ++ tail)) := by
    simp only [fragment0162919Field003Chars00, List.append_assoc]
  calc
    SourceJson.object (fuel + 41) (SourceJson.white (fragment0162919Field003Chars00 ++ tail)) fragment0162919Acc00300 =
        SourceJson.object (fuel + 41)
          (SourceJson.white (fragment0162919Field003HeaderChars00 ++ (fragment0163447Chars ++ (fragment0162919Field003SuffixChars00 ++ tail)))) fragment0162919Acc00300 :=
      congrArg (fun s => SourceJson.object (fuel + 41) (SourceJson.white s) fragment0162919Acc00300) hinput
    _ = (SourceJson.value (fuel + 40) (fragment0163447Chars ++ (fragment0162919Field003SuffixChars00 ++ tail))).bind
        (fragment0162919Field003AfterValue00 (fuel + 40)) := object_fragment0162919_field_003_header fuel (fragment0163447Chars ++ (fragment0162919Field003SuffixChars00 ++ tail))
    _ = (Except.ok (fragment0163447Value, fragment0162919Field003SuffixChars00 ++ tail)).bind (fragment0162919Field003AfterValue00 (fuel + 40)) :=
      congrArg (fun result => result.bind (fragment0162919Field003AfterValue00 (fuel + 40)))
        (value_fragment0163447 (fuel + 0) (fragment0162919Field003SuffixChars00 ++ tail))
    _ = SourceJson.object (fuel + 40) (SourceJson.white tail) fragment0162919Acc00400 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0162919_object_field_003"
  err.flush

noncomputable def fragment0162919Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0162919Field004Value00 : SourceJson := .number (String.ofList ['7', '7'])
noncomputable def fragment0162919Acc00500 : List (String × SourceJson) := (fragment0162919Field004Key00, fragment0162919Field004Value00) :: fragment0162919Acc00400
noncomputable def fragment0162919Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '7', '7', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0162919_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 40) (SourceJson.white (fragment0162919Field004Chars00 ++ tail)) fragment0162919Acc00400 =
      .ok (.obj (fragment0162919Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0162919_object_field_004"
  err.flush

noncomputable def fragment0162919Chars : List Char := '{' :: (fragment0162919Field000Chars00 ++ fragment0162919Field001Chars00 ++ fragment0162919Field002Chars00 ++ fragment0162919Field003Chars00 ++ fragment0162919Field004Chars00)
noncomputable def fragment0162919Value : SourceJson := .obj (fragment0162919Acc00500.reverse)

theorem value_fragment0162919 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 45) (fragment0162919Chars ++ tail) =
      .ok (fragment0162919Value, tail) := by
  have hinput : fragment0162919Chars ++ tail = '{' :: (fragment0162919Field000Chars00 ++ (fragment0162919Field001Chars00 ++ (fragment0162919Field002Chars00 ++ (fragment0162919Field003Chars00 ++ (fragment0162919Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0162919Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 45) (fragment0162919Chars ++ tail) =
        SourceJson.value (fuel + 45) ('{' :: (fragment0162919Field000Chars00 ++ (fragment0162919Field001Chars00 ++ (fragment0162919Field002Chars00 ++ (fragment0162919Field003Chars00 ++ (fragment0162919Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 45)) hinput
    _ = SourceJson.object (fuel + 44) (SourceJson.white (fragment0162919Field000Chars00 ++ (fragment0162919Field001Chars00 ++ (fragment0162919Field002Chars00 ++ (fragment0162919Field003Chars00 ++ (fragment0162919Field004Chars00 ++ (tail))))))) fragment0162919Acc00000 := by rfl
    _ = SourceJson.object (fuel + 43) (SourceJson.white (fragment0162919Field001Chars00 ++ (fragment0162919Field002Chars00 ++ (fragment0162919Field003Chars00 ++ (fragment0162919Field004Chars00 ++ (tail)))))) fragment0162919Acc00100 := object_fragment0162919_field_000 fuel (fragment0162919Field001Chars00 ++ (fragment0162919Field002Chars00 ++ (fragment0162919Field003Chars00 ++ (fragment0162919Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 42) (SourceJson.white (fragment0162919Field002Chars00 ++ (fragment0162919Field003Chars00 ++ (fragment0162919Field004Chars00 ++ (tail))))) fragment0162919Acc00200 := object_fragment0162919_field_001 fuel (fragment0162919Field002Chars00 ++ (fragment0162919Field003Chars00 ++ (fragment0162919Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 41) (SourceJson.white (fragment0162919Field003Chars00 ++ (fragment0162919Field004Chars00 ++ (tail)))) fragment0162919Acc00300 := object_fragment0162919_field_002 fuel (fragment0162919Field003Chars00 ++ (fragment0162919Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 40) (SourceJson.white (fragment0162919Field004Chars00 ++ (tail))) fragment0162919Acc00400 := object_fragment0162919_field_003 fuel (fragment0162919Field004Chars00 ++ (tail))
    _ = .ok (fragment0162919Value, tail) := object_fragment0162919_field_004 fuel (tail)

noncomputable def fragment0162919OpenChars : List Char := ['{']

theorem fragment0162919_open_prefix :
    (sourceRest 162919).take 1 = fragment0162919OpenChars := by rfl

theorem fragment0162919_open_split : sourceRest 162919 = fragment0162919OpenChars ++ sourceRest 162920 := by
  calc
    sourceRest 162919 = (sourceRest 162919).take 1 ++ (sourceRest 162919).drop 1 :=
      (List.take_append_drop 1 (sourceRest 162919)).symm
    _ = fragment0162919OpenChars ++ (sourceRest 162919).drop 1 :=
      congrArg (fun part => part ++ (sourceRest 162919).drop 1) fragment0162919_open_prefix
    _ = fragment0162919OpenChars ++ sourceRest 162920 :=
      congrArg (fun tail => fragment0162919OpenChars ++ tail) (sourceRest_drop 162919 1)

theorem fragment0162919Field000_original_prefix :
    (sourceRest 162920).take 462 = fragment0162919Field000Chars00 := by rfl

theorem fragment0162919Field000_original_split : sourceRest 162920 = fragment0162919Field000Chars00 ++ sourceRest 163382 := by
  calc
    sourceRest 162920 = (sourceRest 162920).take 462 ++ (sourceRest 162920).drop 462 :=
      (List.take_append_drop 462 (sourceRest 162920)).symm
    _ = fragment0162919Field000Chars00 ++ (sourceRest 162920).drop 462 :=
      congrArg (fun part => part ++ (sourceRest 162920).drop 462) fragment0162919Field000_original_prefix
    _ = fragment0162919Field000Chars00 ++ sourceRest 163382 :=
      congrArg (fun tail => fragment0162919Field000Chars00 ++ tail) (sourceRest_drop 162920 462)

theorem fragment0162919Field001_original_prefix :
    (sourceRest 163382).take 23 = fragment0162919Field001Chars00 := by rfl

theorem fragment0162919Field001_original_split : sourceRest 163382 = fragment0162919Field001Chars00 ++ sourceRest 163405 := by
  calc
    sourceRest 163382 = (sourceRest 163382).take 23 ++ (sourceRest 163382).drop 23 :=
      (List.take_append_drop 23 (sourceRest 163382)).symm
    _ = fragment0162919Field001Chars00 ++ (sourceRest 163382).drop 23 :=
      congrArg (fun part => part ++ (sourceRest 163382).drop 23) fragment0162919Field001_original_prefix
    _ = fragment0162919Field001Chars00 ++ sourceRest 163405 :=
      congrArg (fun tail => fragment0162919Field001Chars00 ++ tail) (sourceRest_drop 163382 23)

theorem fragment0162919Field002_original_prefix :
    (sourceRest 163405).take 20 = fragment0162919Field002Chars00 := by rfl

theorem fragment0162919Field002_original_split : sourceRest 163405 = fragment0162919Field002Chars00 ++ sourceRest 163425 := by
  calc
    sourceRest 163405 = (sourceRest 163405).take 20 ++ (sourceRest 163405).drop 20 :=
      (List.take_append_drop 20 (sourceRest 163405)).symm
    _ = fragment0162919Field002Chars00 ++ (sourceRest 163405).drop 20 :=
      congrArg (fun part => part ++ (sourceRest 163405).drop 20) fragment0162919Field002_original_prefix
    _ = fragment0162919Field002Chars00 ++ sourceRest 163425 :=
      congrArg (fun tail => fragment0162919Field002Chars00 ++ tail) (sourceRest_drop 163405 20)

theorem fragment0162919Field003_header_prefix :
    (sourceRest 163425).take 22 = fragment0162919Field003HeaderChars00 := by rfl

theorem fragment0162919Field003_header_split : sourceRest 163425 = fragment0162919Field003HeaderChars00 ++ sourceRest 163447 := by
  calc
    sourceRest 163425 = (sourceRest 163425).take 22 ++ (sourceRest 163425).drop 22 :=
      (List.take_append_drop 22 (sourceRest 163425)).symm
    _ = fragment0162919Field003HeaderChars00 ++ (sourceRest 163425).drop 22 :=
      congrArg (fun part => part ++ (sourceRest 163425).drop 22) fragment0162919Field003_header_prefix
    _ = fragment0162919Field003HeaderChars00 ++ sourceRest 163447 :=
      congrArg (fun tail => fragment0162919Field003HeaderChars00 ++ tail) (sourceRest_drop 163425 22)

theorem fragment0162919Field003_suffix_prefix :
    (sourceRest 167198).take 1 = fragment0162919Field003SuffixChars00 := by rfl

theorem fragment0162919Field003_suffix_split : sourceRest 167198 = fragment0162919Field003SuffixChars00 ++ sourceRest 167199 := by
  calc
    sourceRest 167198 = (sourceRest 167198).take 1 ++ (sourceRest 167198).drop 1 :=
      (List.take_append_drop 1 (sourceRest 167198)).symm
    _ = fragment0162919Field003SuffixChars00 ++ (sourceRest 167198).drop 1 :=
      congrArg (fun part => part ++ (sourceRest 167198).drop 1) fragment0162919Field003_suffix_prefix
    _ = fragment0162919Field003SuffixChars00 ++ sourceRest 167199 :=
      congrArg (fun tail => fragment0162919Field003SuffixChars00 ++ tail) (sourceRest_drop 167198 1)

theorem fragment0162919Field004_original_prefix :
    (sourceRest 167199).take 30 = fragment0162919Field004Chars00 := by rfl

theorem fragment0162919Field004_original_split : sourceRest 167199 = fragment0162919Field004Chars00 ++ sourceRest 167229 := by
  calc
    sourceRest 167199 = (sourceRest 167199).take 30 ++ (sourceRest 167199).drop 30 :=
      (List.take_append_drop 30 (sourceRest 167199)).symm
    _ = fragment0162919Field004Chars00 ++ (sourceRest 167199).drop 30 :=
      congrArg (fun part => part ++ (sourceRest 167199).drop 30) fragment0162919Field004_original_prefix
    _ = fragment0162919Field004Chars00 ++ sourceRest 167229 :=
      congrArg (fun tail => fragment0162919Field004Chars00 ++ tail) (sourceRest_drop 167199 30)

theorem fragment0162919_original_split : sourceRest 162919 = fragment0162919Chars ++ sourceRest 167229 := by
  calc
    sourceRest 162919 = fragment0162919OpenChars ++ (sourceRest 162920) := fragment0162919_open_split
    _ = fragment0162919OpenChars ++ (fragment0162919Field000Chars00 ++ (sourceRest 163382)) := congrArg (fun rest => fragment0162919OpenChars ++ (rest)) fragment0162919Field000_original_split
    _ = fragment0162919OpenChars ++ (fragment0162919Field000Chars00 ++ (fragment0162919Field001Chars00 ++ (sourceRest 163405))) := congrArg (fun rest => fragment0162919OpenChars ++ (fragment0162919Field000Chars00 ++ (rest))) fragment0162919Field001_original_split
    _ = fragment0162919OpenChars ++ (fragment0162919Field000Chars00 ++ (fragment0162919Field001Chars00 ++ (fragment0162919Field002Chars00 ++ (sourceRest 163425)))) := congrArg (fun rest => fragment0162919OpenChars ++ (fragment0162919Field000Chars00 ++ (fragment0162919Field001Chars00 ++ (rest)))) fragment0162919Field002_original_split
    _ = fragment0162919OpenChars ++ (fragment0162919Field000Chars00 ++ (fragment0162919Field001Chars00 ++ (fragment0162919Field002Chars00 ++ (fragment0162919Field003HeaderChars00 ++ (sourceRest 163447))))) := congrArg (fun rest => fragment0162919OpenChars ++ (fragment0162919Field000Chars00 ++ (fragment0162919Field001Chars00 ++ (fragment0162919Field002Chars00 ++ (rest))))) fragment0162919Field003_header_split
    _ = fragment0162919OpenChars ++ (fragment0162919Field000Chars00 ++ (fragment0162919Field001Chars00 ++ (fragment0162919Field002Chars00 ++ (fragment0162919Field003HeaderChars00 ++ (fragment0163447Chars ++ (sourceRest 167198)))))) := congrArg (fun rest => fragment0162919OpenChars ++ (fragment0162919Field000Chars00 ++ (fragment0162919Field001Chars00 ++ (fragment0162919Field002Chars00 ++ (fragment0162919Field003HeaderChars00 ++ (rest)))))) fragment0163447_original_split
    _ = fragment0162919OpenChars ++ (fragment0162919Field000Chars00 ++ (fragment0162919Field001Chars00 ++ (fragment0162919Field002Chars00 ++ (fragment0162919Field003HeaderChars00 ++ (fragment0163447Chars ++ (fragment0162919Field003SuffixChars00 ++ (sourceRest 167199))))))) := congrArg (fun rest => fragment0162919OpenChars ++ (fragment0162919Field000Chars00 ++ (fragment0162919Field001Chars00 ++ (fragment0162919Field002Chars00 ++ (fragment0162919Field003HeaderChars00 ++ (fragment0163447Chars ++ (rest))))))) fragment0162919Field003_suffix_split
    _ = fragment0162919OpenChars ++ (fragment0162919Field000Chars00 ++ (fragment0162919Field001Chars00 ++ (fragment0162919Field002Chars00 ++ (fragment0162919Field003HeaderChars00 ++ (fragment0163447Chars ++ (fragment0162919Field003SuffixChars00 ++ (fragment0162919Field004Chars00 ++ (sourceRest 167229)))))))) := congrArg (fun rest => fragment0162919OpenChars ++ (fragment0162919Field000Chars00 ++ (fragment0162919Field001Chars00 ++ (fragment0162919Field002Chars00 ++ (fragment0162919Field003HeaderChars00 ++ (fragment0163447Chars ++ (fragment0162919Field003SuffixChars00 ++ (rest)))))))) fragment0162919Field004_original_split
    _ = fragment0162919Chars ++ sourceRest 167229 := by simp only [fragment0162919Chars, fragment0162919OpenChars, fragment0162919Field003Chars00, List.cons_append, List.nil_append, List.append_assoc]

theorem value_fragment0162919_original (fuel : Nat) :
    SourceJson.value (fuel + 45) (sourceRest 162919) =
      .ok (fragment0162919Value, sourceRest 167229) :=
  (congrArg (SourceJson.value (fuel + 45)) fragment0162919_original_split).trans
    (value_fragment0162919 fuel (sourceRest 167229))

#print axioms object_fragment0162919_field_000
#print axioms object_fragment0162919_field_001
#print axioms object_fragment0162919_field_002
#print axioms object_fragment0162919_field_003_header
#print axioms object_fragment0162919_field_003
#print axioms object_fragment0162919_field_004
#print axioms value_fragment0162919
#print axioms fragment0162919_open_prefix
#print axioms fragment0162919_open_split
#print axioms fragment0162919Field000_original_prefix
#print axioms fragment0162919Field000_original_split
#print axioms fragment0162919Field001_original_prefix
#print axioms fragment0162919Field001_original_split
#print axioms fragment0162919Field002_original_prefix
#print axioms fragment0162919Field002_original_split
#print axioms fragment0162919Field003_header_prefix
#print axioms fragment0162919Field003_header_split
#print axioms fragment0162919Field003_suffix_prefix
#print axioms fragment0162919Field003_suffix_split
#print axioms fragment0162919Field004_original_prefix
#print axioms fragment0162919Field004_original_split
#print axioms fragment0162919_original_split
#print axioms value_fragment0162919_original

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
