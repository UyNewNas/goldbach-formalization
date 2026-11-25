import ImbalancedChen.P2OriginalSaving19Active8ArrayBlock02000

/-! Compose the complete original active8_enumeration array certificate into its original parent object.
Exact original bytes are candidate data; the original reader equations below
are the Lean checks. No whole-file decide or replacement reader is used. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

def active8HeaderChars00 : List Char := ['\r', '\n', ' ', ' ', '"', 'a', 'c', 't', 'i', 'v', 'e', '8', '_', 'e', 'n', 'u', 'm', 'e', 'r', 'a', 't', 'i', 'o', 'n', '"', ':', ' ']
def active8FieldKey00 : String := String.ofList ['a', 'c', 't', 'i', 'v', 'e', '8', '_', 'e', 'n', 'u', 'm', 'e', 'r', 'a', 't', 'i', 'o', 'n']
def active8FieldAcc00 : List (String × SourceJson) :=
  (active8FieldKey00, active8ArrayValue00) :: normalRankAcc00
def active8SeparatorChars00 : List Char := [',']

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 active8_field_after_data"
  err.flush

theorem geometryChars00_active8_header_prefix :
    (geometryChars00.drop 380).take 27 = active8HeaderChars00 := by rfl

theorem geometryChars00_active8_header_split :
    geometryChars00.drop 380 = active8HeaderChars00 ++ geometryChars00.drop 407 := by
  calc
    geometryChars00.drop 380 =
        (geometryChars00.drop 380).take 27 ++ (geometryChars00.drop 380).drop 27 :=
      (List.take_append_drop 27 (geometryChars00.drop 380)).symm
    _ = active8HeaderChars00 ++ (geometryChars00.drop 380).drop 27 :=
      congrArg (fun p => p ++ (geometryChars00.drop 380).drop 27) geometryChars00_active8_header_prefix
    _ = active8HeaderChars00 ++ geometryChars00.drop 407 := by rw [List.drop_drop]

theorem geometryChars00_active8_separator_prefix :
    (geometryChars00.drop 40597).take 1 = active8SeparatorChars00 := by rfl

theorem geometryChars00_active8_separator_split :
    geometryChars00.drop 40597 = active8SeparatorChars00 ++ geometryChars00.drop 40598 := by
  calc
    geometryChars00.drop 40597 =
        (geometryChars00.drop 40597).take 1 ++ (geometryChars00.drop 40597).drop 1 :=
      (List.take_append_drop 1 (geometryChars00.drop 40597)).symm
    _ = active8SeparatorChars00 ++ (geometryChars00.drop 40597).drop 1 :=
      congrArg (fun p => p ++ (geometryChars00.drop 40597).drop 1) geometryChars00_active8_separator_prefix
    _ = active8SeparatorChars00 ++ geometryChars00.drop 40598 := by rw [List.drop_drop]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 active8_field_after_raw_bindings"
  err.flush

def active8AfterValue00 (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending =>
      .ok (.obj (((active8FieldKey00, result.1) :: normalRankAcc00).reverse), ending)
  | ',' :: ending =>
      SourceJson.object fuel (SourceJson.white ending)
        ((active8FieldKey00, result.1) :: normalRankAcc00)
  | _ => .error "object separator missing"

theorem object_active8_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 195) (SourceJson.white (active8HeaderChars00 ++ rest)) normalRankAcc00 =
      (SourceJson.value (fuel + 194) rest).bind (active8AfterValue00 (fuel + 194)) := by rfl

theorem active8_after_value_separator (fuel : Nat) (tail : List Char) :
    (Except.ok (active8ArrayValue00, active8SeparatorChars00 ++ tail)).bind
      (active8AfterValue00 (fuel + 194)) =
      SourceJson.object (fuel + 194) (SourceJson.white tail) active8FieldAcc00 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 active8_field_after_generic_continuation"
  err.flush


theorem object_active8_original (fuel : Nat) :
    SourceJson.object (fuel + 195) (SourceJson.white (geometryChars00.drop 380)) normalRankAcc00 =
      SourceJson.object (fuel + 194) (SourceJson.white (geometryChars00.drop 40598)) active8FieldAcc00 := by
  calc
    SourceJson.object (fuel + 195) (SourceJson.white (geometryChars00.drop 380)) normalRankAcc00 =
        SourceJson.object (fuel + 195)
          (SourceJson.white (active8HeaderChars00 ++ geometryChars00.drop 407)) normalRankAcc00 :=
      congrArg (fun s => SourceJson.object (fuel + 195) (SourceJson.white s) normalRankAcc00)
        geometryChars00_active8_header_split
    _ = (SourceJson.value (fuel + 194) (geometryChars00.drop 407)).bind
        (active8AfterValue00 (fuel + 194)) :=
      object_active8_header fuel (geometryChars00.drop 407)
    _ = (Except.ok (active8ArrayValue00, geometryChars00.drop 40597)).bind
        (active8AfterValue00 (fuel + 194)) :=
      congrArg (fun result => result.bind (active8AfterValue00 (fuel + 194)))
        (value_active8_original (fuel + 0))
    _ = (Except.ok (active8ArrayValue00,
          active8SeparatorChars00 ++ geometryChars00.drop 40598)).bind
        (active8AfterValue00 (fuel + 194)) :=
      congrArg (fun rest => (Except.ok (active8ArrayValue00, rest)).bind
        (active8AfterValue00 (fuel + 194))) geometryChars00_active8_separator_split
    _ = SourceJson.object (fuel + 194)
        (SourceJson.white (geometryChars00.drop 40598)) active8FieldAcc00 :=
      active8_after_value_separator fuel (geometryChars00.drop 40598)

theorem geometryChars00_through_active8 :
    SourceJson.value 195135 geometryChars00 =
      SourceJson.object 195128 (SourceJson.white (geometryChars00.drop 40598)) active8FieldAcc00 := by
  exact geometryChars00_through_normal_rank.trans (object_active8_original 194934)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 active8_field_complete"
  err.flush

#print axioms geometryChars00_active8_header_prefix
#print axioms geometryChars00_active8_header_split
#print axioms geometryChars00_active8_separator_prefix
#print axioms geometryChars00_active8_separator_split
#print axioms object_active8_header
#print axioms active8_after_value_separator
#print axioms object_active8_original
#print axioms geometryChars00_through_active8

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
