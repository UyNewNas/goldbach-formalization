import Lean

/- Diagnostic only: exact small SourceJson scalar/array definitions, with a Nat-valued
   stand-in for rational decoding. No Mathlib imports and no production theorem. -/
namespace FieldPreorderProbe
inductive Json where
  | number (token : String)
  | str (s : String)
  | arr (items : List Json)
class Decode (α : Type) where
  read : Json → Except String α

def getStr : Json → Except String String
  | .str s => .ok s
  | _ => .error "expected original JSON string"
def getArr : Json → Except String (Array Json)
  | .arr xs => .ok xs.toArray
  | _ => .error "expected original JSON array"
def digitsNat : List Char → Nat → Option Nat :=
  List.rec (motive := fun _ => Nat → Option Nat)
    (fun acc => some acc)
    (fun c _ previous acc =>
      if 48 ≤ c.toNat ∧ c.toNat ≤ 57 then
        previous (10 * acc + (c.toNat - 48))
      else none)
def natChars (cs : List Char) : Option Nat :=
  if cs.isEmpty then none else digitsNat cs 0
instance : Decode Nat where
  read := fun j => match j with
    | .number s => match natChars s.toList with
      | some n => .ok n
      | none => .error "expected original natural number"
    | _ => .error "expected original integer token"
instance : Decode String where
  read := getStr
instance [Decode α] : Decode (Array α) where
  read := fun j => do (← getArr j).mapM Decode.read

theorem decodeNat_number_ofList (cs : List Char) :
    (Decode.read (.number (String.ofList cs)) : Except String Nat) =
      match natChars cs with
      | some n => .ok n
      | none => .error "expected original natural number" := by
  change (match natChars (String.ofList cs).toList with
    | some n => Except.ok n
    | none => Except.error "expected original natural number") = _
  rw [String.toList_ofList]
theorem decodeString_str (s : String) :
    (Decode.read (.str s) : Except String String) = .ok s := rfl
theorem decodeArray_arr {α : Type} [Decode α] (items : List Json) :
    (Decode.read (.arr items) : Except String (Array α)) =
      List.toArray <$> items.mapM Decode.read := by
  change items.toArray.mapM Decode.read = _
  exact List.mapM_toArray

def token (s : String) : Except String Nat := .ok s.length
def tokenArray (j : Json) : Except String (Array Nat) := do
  (← getArr j).mapM fun v => do token (← getStr v)
theorem tokenArray_arr (items : List Json) :
    tokenArray (.arr items) = List.toArray <$> items.mapM (fun v => do token (← getStr v)) := by
  change items.toArray.mapM (fun v => do token (← getStr v)) = _
  exact List.mapM_toArray

private theorem except_ok_bind {α β : Type} (a : α) (f : α → Except String β) :
    ((Except.ok a : Except String α) >>= f) = f a := rfl
private theorem except_ok_map {α β : Type} (a : α) (f : α → β) :
    f <$> (Except.ok a : Except String α) = .ok (f a) := rfl
private theorem except_pure_eq_ok {α : Type} (a : α) :
    (pure a : Except String α) = .ok a := rfl
attribute [local simp] except_ok_bind except_ok_map except_pure_eq_ok
attribute [local simp] decodeString_str decodeArray_arr tokenArray_arr getStr getArr natChars digitsNat
theorem token000_decoded : token (String.ofList ['1']) = .ok 1 := by rfl
theorem token001_decoded : token (String.ofList ['8', '/', '7']) = .ok 3 := by rfl
theorem token002_decoded : token (String.ofList ['1', '6', '/', '7']) = .ok 4 := by rfl
theorem token003_decoded : token (String.ofList ['1', '/', '7']) = .ok 3 := by rfl
theorem token004_decoded : token (String.ofList ['4', '0', '/', '7']) = .ok 4 := by rfl
theorem token005_decoded : token (String.ofList ['2', '0', '/', '7']) = .ok 4 := by rfl
theorem token006_decoded : token (String.ofList ['6', '/', '7']) = .ok 3 := by rfl
theorem token007_decoded : token (String.ofList ['3', '4', '/', '2', '1']) = .ok 5 := by rfl
theorem token008_decoded : token (String.ofList ['4']) = .ok 1 := by rfl
theorem token009_decoded : token (String.ofList ['5', '8', '5', '9', '4', '2', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0']) = .ok 16 := by rfl
theorem token010_decoded : token (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '1', '2', '0', '0', '0', '0', '0', '0']) = .ok 16 := by rfl
theorem token011_decoded : token (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0']) = .ok 16 := by rfl
theorem token012_decoded : token (String.ofList ['1', '1', '7', '1', '8', '2', '3', '/', '3', '6', '0', '0', '0', '0', '0', '0']) = .ok 16 := by rfl
theorem token013_decoded : token (String.ofList ['2', '7', '6', '5', '6', '7', '7', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']) = .ok 17 := by rfl
theorem token014_decoded : token (String.ofList ['6', '6', '1', '3', '3', '6', '1', '/', '8', '4', '0', '0', '0', '0', '0', '0']) = .ok 16 := by rfl
theorem token015_decoded : token (String.ofList ['5', '2', '2', '5', '8', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']) = .ok 15 := by rfl
theorem token016_decoded : token (String.ofList ['2', '4', '8', '4', '4', '9', '1', '/', '4', '2', '0', '0', '0', '0', '0', '0']) = .ok 16 := by rfl
theorem token017_decoded : token (String.ofList ['0']) = .ok 1 := by rfl
theorem token018_decoded : token (String.ofList ['1', '0', '9', '3', '8', '3', '/', '2', '0', '0', '0', '0', '0', '0']) = .ok 14 := by rfl
theorem token019_decoded : token (String.ofList ['7', '9', '6', '8', '7', '9', '/', '9', '0', '0', '0', '0', '0', '0']) = .ok 14 := by rfl
theorem token020_decoded : token (String.ofList ['3', '9', '8', '4', '3', '0', '7', '/', '1', '2', '2', '0', '0', '0', '0', '0', '0']) = .ok 17 := by rfl
theorem token021_decoded : token (String.ofList ['2', '8', '1', '2', '6', '3', '/', '3', '0', '0', '0', '0', '0', '0']) = .ok 14 := by rfl
theorem token022_decoded : token (String.ofList ['2', '0', '1', '5', '8', '1', '3', '/', '5', '4', '0', '0', '0', '0', '0', '0']) = .ok 16 := by rfl
theorem token023_decoded : token (String.ofList ['1', '/', '7', '5', '0', '0', '0', '0']) = .ok 8 := by rfl
theorem token024_decoded : token (String.ofList ['7', '4', '5', '3', '1', '3', '7', '/', '2', '2', '4', '0', '0', '0', '0', '0', '0']) = .ok 17 := by rfl
theorem token025_decoded : token (String.ofList ['2', '7', '8', '9', '0', '6', '2', '1', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']) = .ok 18 := by rfl
theorem token026_decoded : token (String.ofList ['3', '2', '8', '1', '2', '9', '/', '1', '5', '0', '0', '0', '0', '0']) = .ok 14 := by rfl
theorem token027_decoded : token (String.ofList ['5', '2', '9', '6', '9', '6', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0']) = .ok 16 := by rfl
theorem token028_decoded : token (String.ofList ['3', '2', '7', '9', '6', '5', '4', '3', '/', '2', '4', '4', '0', '0', '0', '0', '0', '0']) = .ok 18 := by rfl
theorem token029_decoded : token (String.ofList ['1', '2', '9', '6', '8', '6', '1', '/', '1', '2', '2', '0', '0', '0', '0', '0']) = .ok 16 := by rfl
theorem token030_decoded : token (String.ofList ['8', '9', '0', '6', '5', '9', '/', '6', '0', '0', '0', '0', '0', '0']) = .ok 14 := by rfl
theorem token031_decoded : token (String.ofList ['1', '4', '5', '3', '1', '9', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0']) = .ok 16 := by rfl
theorem token032_decoded : token (String.ofList ['1', '5', '4', '6', '9', '0', '9', '/', '1', '2', '0', '0', '0', '0', '0', '0']) = .ok 16 := by rfl
theorem token033_decoded : token (String.ofList ['3', '8', '0', '8', '7', '/', '3', '7', '5', '0', '0', '0']) = .ok 12 := by rfl
theorem token034_decoded : token (String.ofList ['2', '7', '6', '5', '6', '7', '7', '/', '2', '7', '0', '0', '0', '0', '0', '0']) = .ok 16 := by rfl
theorem token035_decoded : token (String.ofList ['2', '7', '6', '5', '6', '7', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0']) = .ok 16 := by rfl
theorem token036_decoded : token (String.ofList ['7', '5', '4', '7', '1', '6', '7', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']) = .ok 17 := by rfl
theorem token037_decoded : token (String.ofList ['1', '5', '9', '3', '8', '3', '/', '3', '6', '0', '0', '0', '0', '0']) = .ok 14 := by rfl
theorem token038_decoded : token (String.ofList ['7', '9', '6', '9', '2', '7', '/', '1', '8', '0', '0', '0', '0', '0', '0']) = .ok 15 := by rfl
theorem token039_decoded : token (String.ofList ['5', '3', '5', '9', '2', '5', '1', '/', '4', '8', '8', '0', '0', '0', '0', '0', '0']) = .ok 17 := by rfl
theorem token040_decoded : token (String.ofList ['2', '4', '8', '4', '3', '7', '9', '/', '5', '6', '0', '0', '0', '0', '0', '0']) = .ok 16 := by rfl
theorem token041_decoded : token (String.ofList ['2', '3', '4', '3', '7', '9', '/', '2', '4', '0', '0', '0', '0', '0']) = .ok 14 := by rfl
theorem token042_decoded : token (String.ofList ['2', '2', '0', '7', '8', '0', '4', '1', '/', '4', '8', '8', '0', '0', '0', '0', '0', '0']) = .ok 18 := by rfl
theorem token043_decoded : token (String.ofList ['2', '4', '8', '4', '4', '9', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']) = .ok 16 := by rfl
theorem token044_decoded : token (String.ofList ['5', '8', '5', '9', '4', '2', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0']) = .ok 16 := by rfl
theorem token045_decoded : token (String.ofList ['3', '6', '5', '6', '2', '9', '/', '4', '8', '0', '0', '0', '0', '0']) = .ok 14 := by rfl
theorem token046_decoded : token (String.ofList ['3', '2', '8', '1', '3', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0']) = .ok 15 := by rfl
theorem token047_decoded : token (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '8', '0', '0', '0', '0', '0', '0']) = .ok 15 := by rfl
theorem token048_decoded : token (String.ofList ['7', '4', '5', '3', '3', '6', '1', '/', '5', '6', '0', '0', '0', '0', '0', '0']) = .ok 16 := by rfl
theorem token049_decoded : token (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '4', '0', '0', '0', '0', '0', '0']) = .ok 15 := by rfl
theorem token050_decoded : token (String.ofList ['3', '8', '7', '9', '6', '8', '3', '1', '/', '4', '8', '8', '0', '0', '0', '0', '0', '0']) = .ok 18 := by rfl
theorem token051_decoded : token (String.ofList ['2', '4', '8', '4', '3', '7', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0']) = .ok 16 := by rfl
theorem token052_decoded : token (String.ofList ['7', '3', '5', '9', '3', '4', '7', '/', '2', '4', '4', '0', '0', '0', '0', '0', '0']) = .ok 17 := by rfl
theorem token053_decoded : token (String.ofList ['3', '2', '8', '1', '3', '3', '/', '8', '0', '0', '0', '0', '0', '0']) = .ok 14 := by rfl
theorem token054_decoded : token (String.ofList ['1', '2', '5', '0', '0', '1', '/', '2', '0', '0', '0', '0', '0', '0']) = .ok 14 := by rfl
theorem token055_decoded : token (String.ofList ['3', '2', '8', '1', '3', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0']) = .ok 15 := by rfl
theorem token056_decoded : token (String.ofList ['2', '6', '7', '1', '8', '8', '3', '/', '1', '4', '0', '0', '0', '0', '0', '0']) = .ok 16 := by rfl
theorem token057_decoded : token (String.ofList ['4', '9', '6', '8', '8', '7', '/', '2', '8', '0', '0', '0', '0', '0']) = .ok 14 := by rfl
theorem token058_decoded : token (String.ofList ['2', '4', '8', '4', '3', '7', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0']) = .ok 16 := by rfl
theorem token059_decoded : token (String.ofList ['3', '7', '7', '8', '1', '3', '7', '/', '1', '1', '2', '0', '0', '0', '0', '0']) = .ok 16 := by rfl
theorem token060_decoded : token (String.ofList ['7', '8', '5', '9', '3', '7', '1', '/', '1', '2', '2', '0', '0', '0', '0', '0', '0']) = .ok 17 := by rfl
theorem token061_decoded : token (String.ofList ['2', '4', '8', '4', '3', '7', '9', '/', '1', '6', '8', '0', '0', '0', '0', '0', '0']) = .ok 17 := by rfl
theorem token062_decoded : token (String.ofList ['3', '7', '5', '0', '0', '3', '/', '2', '0', '0', '0', '0', '0', '0']) = .ok 14 := by rfl
theorem token063_decoded : token (String.ofList ['7', '3', '5', '9', '3', '4', '7', '/', '4', '8', '8', '0', '0', '0', '0', '0', '0']) = .ok 17 := by rfl
theorem token064_decoded : token (String.ofList ['3', '2', '8', '1', '3', '3', '/', '4', '0', '0', '0', '0', '0', '0']) = .ok 14 := by rfl
theorem token065_decoded : token (String.ofList ['2', '6', '7', '1', '8', '9', '1', '/', '8', '0', '0', '0', '0', '0', '0']) = .ok 15 := by rfl
theorem token066_decoded : token (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0']) = .ok 16 := by rfl
theorem token067_decoded : token (String.ofList ['1', '3', '1', '7', '1', '9', '1', '1', '/', '5', '6', '0', '0', '0', '0', '0', '0']) = .ok 17 := by rfl
theorem token068_decoded : token (String.ofList ['1', '2', '4', '2', '2', '1', '1', '9', '/', '5', '6', '0', '0', '0', '0', '0', '0']) = .ok 17 := by rfl
theorem token069_decoded : token (String.ofList ['7', '4', '5', '3', '1', '3', '7', '/', '5', '6', '0', '0', '0', '0', '0', '0']) = .ok 16 := by rfl
theorem token070_decoded : token (String.ofList ['2', '6', '7', '1', '8', '8', '3', '/', '7', '0', '0', '0', '0', '0', '0']) = .ok 15 := by rfl

attribute [local simp] decodeNat_number_ofList
attribute [local simp] token000_decoded token001_decoded token002_decoded token003_decoded token004_decoded token005_decoded token006_decoded token007_decoded token008_decoded token009_decoded token010_decoded token011_decoded token012_decoded token013_decoded token014_decoded token015_decoded token016_decoded token017_decoded token018_decoded token019_decoded token020_decoded token021_decoded token022_decoded token023_decoded token024_decoded token025_decoded token026_decoded token027_decoded token028_decoded token029_decoded token030_decoded token031_decoded token032_decoded token033_decoded token034_decoded token035_decoded token036_decoded token037_decoded token038_decoded token039_decoded token040_decoded token041_decoded token042_decoded token043_decoded token044_decoded token045_decoded token046_decoded token047_decoded token048_decoded token049_decoded token050_decoded token051_decoded token052_decoded token053_decoded token054_decoded token055_decoded token056_decoded token057_decoded token058_decoded token059_decoded token060_decoded token061_decoded token062_decoded token063_decoded token064_decoded token065_decoded token066_decoded token067_decoded token068_decoded token069_decoded token070_decoded

theorem nat0 : (Decode.read (.number (String.ofList ['0'])) : Except String Nat) = .ok 0 := by simp
theorem nat8 : (Decode.read (.number (String.ofList ['8'])) : Except String Nat) = .ok 8 := by simp
theorem nat1 : (Decode.read (.number (String.ofList ['1'])) : Except String Nat) = .ok 1 := by simp
theorem left_masks : (Decode.read (.arr [(.number (String.ofList ['1'])), (.number (String.ofList ['2'])), (.number (String.ofList ['4'])), (.number (String.ofList ['8'])), (.number (String.ofList ['1', '0'])), (.number (String.ofList ['1', '2'])), (.number (String.ofList ['1', '6'])), (.number (String.ofList ['1', '8'])), (.number (String.ofList ['2', '0'])), (.number (String.ofList ['2', '4'])), (.number (String.ofList ['2', '6'])), (.number (String.ofList ['2', '8'])), (.number (String.ofList ['3', '2'])), (.number (String.ofList ['3', '4'])), (.number (String.ofList ['3', '6'])), (.number (String.ofList ['4', '0'])), (.number (String.ofList ['4', '2'])), (.number (String.ofList ['4', '4'])), (.number (String.ofList ['4', '8'])), (.number (String.ofList ['5', '0'])), (.number (String.ofList ['5', '2'])), (.number (String.ofList ['5', '6'])), (.number (String.ofList ['5', '8'])), (.number (String.ofList ['6', '0']))]) : Except String (Array Nat)) = .ok #[1, 2, 4, 8, 10, 12, 16, 18, 20, 24, 26, 28, 32, 34, 36, 40, 42, 44, 48, 50, 52, 56, 58, 60] := by
  simp

theorem right_masks : (Decode.read (.arr [(.number (String.ofList ['3'])), (.number (String.ofList ['5'])), (.number (String.ofList ['6'])), (.number (String.ofList ['7'])), (.number (String.ofList ['9'])), (.number (String.ofList ['1', '1'])), (.number (String.ofList ['1', '3'])), (.number (String.ofList ['1', '4'])), (.number (String.ofList ['1', '5'])), (.number (String.ofList ['1', '7'])), (.number (String.ofList ['1', '9'])), (.number (String.ofList ['2', '1'])), (.number (String.ofList ['2', '2'])), (.number (String.ofList ['2', '3'])), (.number (String.ofList ['2', '5'])), (.number (String.ofList ['2', '7'])), (.number (String.ofList ['2', '9'])), (.number (String.ofList ['3', '0'])), (.number (String.ofList ['3', '1'])), (.number (String.ofList ['3', '3'])), (.number (String.ofList ['3', '5'])), (.number (String.ofList ['3', '7'])), (.number (String.ofList ['3', '8'])), (.number (String.ofList ['3', '9'])), (.number (String.ofList ['4', '1'])), (.number (String.ofList ['4', '3'])), (.number (String.ofList ['4', '5'])), (.number (String.ofList ['4', '6'])), (.number (String.ofList ['4', '7'])), (.number (String.ofList ['4', '9'])), (.number (String.ofList ['5', '1'])), (.number (String.ofList ['5', '3'])), (.number (String.ofList ['5', '4'])), (.number (String.ofList ['5', '5'])), (.number (String.ofList ['5', '7'])), (.number (String.ofList ['5', '9'])), (.number (String.ofList ['6', '1'])), (.number (String.ofList ['6', '2'])), (.number (String.ofList ['6', '3']))]) : Except String (Array Nat)) = .ok #[3, 5, 6, 7, 9, 11, 13, 14, 15, 17, 19, 21, 22, 23, 25, 27, 29, 30, 31, 33, 35, 37, 38, 39, 41, 43, 45, 46, 47, 49, 51, 53, 54, 55, 57, 59, 61, 62, 63] := by
  simp

theorem facet_original_indices : (Decode.read (.arr [(.number (String.ofList ['4'])), (.number (String.ofList ['6'])), (.number (String.ofList ['7'])), (.number (String.ofList ['8'])), (.number (String.ofList ['9'])), (.number (String.ofList ['1', '6'])), (.number (String.ofList ['1', '7'])), (.number (String.ofList ['3', '3'])), (.number (String.ofList ['6', '5'])), (.number (String.ofList ['9', '0']))]) : Except String (Array Nat)) = .ok #[4, 6, 7, 8, 9, 16, 17, 33, 65, 90] := by
  simp

theorem facet_vertices : (Decode.read (.arr [(.arr [(.number (String.ofList ['0'])), (.number (String.ofList ['1'])), (.number (String.ofList ['2'])), (.number (String.ofList ['3'])), (.number (String.ofList ['4'])), (.number (String.ofList ['6'])), (.number (String.ofList ['8'])), (.number (String.ofList ['9'])), (.number (String.ofList ['1', '0'])), (.number (String.ofList ['1', '1'])), (.number (String.ofList ['1', '2'])), (.number (String.ofList ['1', '3'])), (.number (String.ofList ['1', '4'])), (.number (String.ofList ['1', '5']))]), (.arr [(.number (String.ofList ['0'])), (.number (String.ofList ['1'])), (.number (String.ofList ['2'])), (.number (String.ofList ['3'])), (.number (String.ofList ['4'])), (.number (String.ofList ['5'])), (.number (String.ofList ['6'])), (.number (String.ofList ['7'])), (.number (String.ofList ['8'])), (.number (String.ofList ['9'])), (.number (String.ofList ['1', '0'])), (.number (String.ofList ['1', '1'])), (.number (String.ofList ['1', '3'])), (.number (String.ofList ['1', '5']))]), (.arr [(.number (String.ofList ['0'])), (.number (String.ofList ['1'])), (.number (String.ofList ['2'])), (.number (String.ofList ['3'])), (.number (String.ofList ['4'])), (.number (String.ofList ['5'])), (.number (String.ofList ['6'])), (.number (String.ofList ['7'])), (.number (String.ofList ['8'])), (.number (String.ofList ['9'])), (.number (String.ofList ['1', '0'])), (.number (String.ofList ['1', '2'])), (.number (String.ofList ['1', '4'])), (.number (String.ofList ['1', '5']))]), (.arr [(.number (String.ofList ['1'])), (.number (String.ofList ['3'])), (.number (String.ofList ['6'])), (.number (String.ofList ['7'])), (.number (String.ofList ['9'])), (.number (String.ofList ['1', '3'])), (.number (String.ofList ['1', '4'])), (.number (String.ofList ['1', '5']))]), (.arr [(.number (String.ofList ['0'])), (.number (String.ofList ['2'])), (.number (String.ofList ['4'])), (.number (String.ofList ['5'])), (.number (String.ofList ['8'])), (.number (String.ofList ['1', '0'])), (.number (String.ofList ['1', '1'])), (.number (String.ofList ['1', '2']))]), (.arr [(.number (String.ofList ['0'])), (.number (String.ofList ['1'])), (.number (String.ofList ['2'])), (.number (String.ofList ['3'])), (.number (String.ofList ['4'])), (.number (String.ofList ['5'])), (.number (String.ofList ['6'])), (.number (String.ofList ['7'])), (.number (String.ofList ['1', '0'])), (.number (String.ofList ['1', '1'])), (.number (String.ofList ['1', '2'])), (.number (String.ofList ['1', '3'])), (.number (String.ofList ['1', '4'])), (.number (String.ofList ['1', '5']))]), (.arr [(.number (String.ofList ['0'])), (.number (String.ofList ['1'])), (.number (String.ofList ['4'])), (.number (String.ofList ['5'])), (.number (String.ofList ['6'])), (.number (String.ofList ['7'])), (.number (String.ofList ['8'])), (.number (String.ofList ['9'])), (.number (String.ofList ['1', '0'])), (.number (String.ofList ['1', '1'])), (.number (String.ofList ['1', '2'])), (.number (String.ofList ['1', '3'])), (.number (String.ofList ['1', '4'])), (.number (String.ofList ['1', '5']))]), (.arr [(.number (String.ofList ['2'])), (.number (String.ofList ['3'])), (.number (String.ofList ['4'])), (.number (String.ofList ['5'])), (.number (String.ofList ['6'])), (.number (String.ofList ['7'])), (.number (String.ofList ['8'])), (.number (String.ofList ['9'])), (.number (String.ofList ['1', '0'])), (.number (String.ofList ['1', '1'])), (.number (String.ofList ['1', '2'])), (.number (String.ofList ['1', '3'])), (.number (String.ofList ['1', '4'])), (.number (String.ofList ['1', '5']))]), (.arr [(.number (String.ofList ['0'])), (.number (String.ofList ['1'])), (.number (String.ofList ['2'])), (.number (String.ofList ['3'])), (.number (String.ofList ['4'])), (.number (String.ofList ['5'])), (.number (String.ofList ['6'])), (.number (String.ofList ['7'])), (.number (String.ofList ['8'])), (.number (String.ofList ['9'])), (.number (String.ofList ['1', '1'])), (.number (String.ofList ['1', '2'])), (.number (String.ofList ['1', '3'])), (.number (String.ofList ['1', '4']))]), (.arr [(.number (String.ofList ['0'])), (.number (String.ofList ['1'])), (.number (String.ofList ['2'])), (.number (String.ofList ['3'])), (.number (String.ofList ['5'])), (.number (String.ofList ['7'])), (.number (String.ofList ['8'])), (.number (String.ofList ['9'])), (.number (String.ofList ['1', '0'])), (.number (String.ofList ['1', '1'])), (.number (String.ofList ['1', '2'])), (.number (String.ofList ['1', '3'])), (.number (String.ofList ['1', '4'])), (.number (String.ofList ['1', '5']))])]) : Except String (Array (Array Nat))) = .ok #[#[0, 1, 2, 3, 4, 6, 8, 9, 10, 11, 12, 13, 14, 15], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15], #[1, 3, 6, 7, 9, 13, 14, 15], #[0, 2, 4, 5, 8, 10, 11, 12], #[0, 1, 2, 3, 4, 5, 6, 7, 10, 11, 12, 13, 14, 15], #[0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], #[2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14], #[0, 1, 2, 3, 5, 7, 8, 9, 10, 11, 12, 13, 14, 15]] := by
  simp

theorem balance : tokenArray (.arr [(.str (String.ofList ['1'])), (.str (String.ofList ['8', '/', '7'])), (.str (String.ofList ['1', '6', '/', '7'])), (.str (String.ofList ['1'])), (.str (String.ofList ['1', '/', '7'])), (.str (String.ofList ['4', '0', '/', '7'])), (.str (String.ofList ['2', '0', '/', '7'])), (.str (String.ofList ['6', '/', '7'])), (.str (String.ofList ['3', '4', '/', '2', '1'])), (.str (String.ofList ['4']))]) = .ok #[1, 3, 4, 1, 3, 4, 4, 3, 5, 1] := by
  simp

theorem vertex : tokenArray (.arr [(.str (String.ofList ['5', '8', '5', '9', '4', '2', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '1', '2', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '1', '2', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['1', '1', '7', '1', '8', '2', '3', '/', '3', '6', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['1', '1', '7', '1', '8', '2', '3', '/', '3', '6', '0', '0', '0', '0', '0', '0']))]) = .ok #[16, 16, 16, 16, 16, 16, 16, 16] := by
  simp

theorem minima : tokenArray (.arr [(.str (String.ofList ['2', '7', '6', '5', '6', '7', '7', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['6', '6', '1', '3', '3', '6', '1', '/', '8', '4', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['5', '2', '2', '5', '8', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['2', '4', '8', '4', '4', '9', '1', '/', '4', '2', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['0'])), (.str (String.ofList ['1', '0', '9', '3', '8', '3', '/', '2', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['0'])), (.str (String.ofList ['0'])), (.str (String.ofList ['0'])), (.str (String.ofList ['0'])), (.str (String.ofList ['7', '9', '6', '8', '7', '9', '/', '9', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['3', '9', '8', '4', '3', '0', '7', '/', '1', '2', '2', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['2', '8', '1', '2', '6', '3', '/', '3', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['2', '0', '1', '5', '8', '1', '3', '/', '5', '4', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['1', '/', '7', '5', '0', '0', '0', '0'])), (.str (String.ofList ['7', '4', '5', '3', '1', '3', '7', '/', '2', '2', '4', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['0'])), (.str (String.ofList ['0'])), (.str (String.ofList ['2', '7', '8', '9', '0', '6', '2', '1', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['3', '2', '8', '1', '2', '9', '/', '1', '5', '0', '0', '0', '0', '0'])), (.str (String.ofList ['5', '2', '9', '6', '9', '6', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['3', '2', '7', '9', '6', '5', '4', '3', '/', '2', '4', '4', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['1', '2', '9', '6', '8', '6', '1', '/', '1', '2', '2', '0', '0', '0', '0', '0'])), (.str (String.ofList ['8', '9', '0', '6', '5', '9', '/', '6', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['1', '4', '5', '3', '1', '9', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['1', '5', '4', '6', '9', '0', '9', '/', '1', '2', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['3', '8', '0', '8', '7', '/', '3', '7', '5', '0', '0', '0'])), (.str (String.ofList ['2', '7', '6', '5', '6', '7', '7', '/', '2', '7', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['2', '7', '6', '5', '6', '7', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['7', '5', '4', '7', '1', '6', '7', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['1', '5', '9', '3', '8', '3', '/', '3', '6', '0', '0', '0', '0', '0'])), (.str (String.ofList ['7', '9', '6', '9', '2', '7', '/', '1', '8', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['7', '9', '6', '9', '2', '7', '/', '1', '8', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['0'])), (.str (String.ofList ['5', '3', '5', '9', '2', '5', '1', '/', '4', '8', '8', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['2', '4', '8', '4', '3', '7', '9', '/', '5', '6', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['2', '3', '4', '3', '7', '9', '/', '2', '4', '0', '0', '0', '0', '0'])), (.str (String.ofList ['2', '2', '0', '7', '8', '0', '4', '1', '/', '4', '8', '8', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['2', '4', '8', '4', '4', '9', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['5', '8', '5', '9', '4', '2', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['3', '6', '5', '6', '2', '9', '/', '4', '8', '0', '0', '0', '0', '0'])), (.str (String.ofList ['0'])), (.str (String.ofList ['3', '2', '8', '1', '3', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '8', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['3', '2', '8', '1', '3', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['7', '4', '5', '3', '3', '6', '1', '/', '5', '6', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['2', '4', '8', '4', '3', '7', '9', '/', '5', '6', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '4', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['3', '8', '7', '9', '6', '8', '3', '1', '/', '4', '8', '8', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['0'])), (.str (String.ofList ['2', '4', '8', '4', '3', '7', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '8', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['7', '3', '5', '9', '3', '4', '7', '/', '2', '4', '4', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['7', '4', '5', '3', '3', '6', '1', '/', '5', '6', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['3', '2', '8', '1', '3', '3', '/', '8', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '4', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['1', '2', '5', '0', '0', '1', '/', '2', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['2', '4', '8', '4', '3', '7', '9', '/', '5', '6', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['3', '2', '8', '1', '3', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['2', '6', '7', '1', '8', '8', '3', '/', '1', '4', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['3', '2', '8', '1', '3', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['4', '9', '6', '8', '8', '7', '/', '2', '8', '0', '0', '0', '0', '0'])), (.str (String.ofList ['2', '4', '8', '4', '3', '7', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['3', '7', '7', '8', '1', '3', '7', '/', '1', '1', '2', '0', '0', '0', '0', '0'])), (.str (String.ofList ['3', '8', '7', '9', '6', '8', '3', '1', '/', '4', '8', '8', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['0'])), (.str (String.ofList ['2', '4', '8', '4', '3', '7', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '8', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['7', '3', '5', '9', '3', '4', '7', '/', '2', '4', '4', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['7', '4', '5', '3', '3', '6', '1', '/', '5', '6', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['3', '2', '8', '1', '3', '3', '/', '8', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '4', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['1', '2', '5', '0', '0', '1', '/', '2', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['2', '4', '8', '4', '3', '7', '9', '/', '5', '6', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['3', '2', '8', '1', '3', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['2', '6', '7', '1', '8', '8', '3', '/', '1', '4', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['3', '2', '8', '1', '3', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['4', '9', '6', '8', '8', '7', '/', '2', '8', '0', '0', '0', '0', '0'])), (.str (String.ofList ['2', '4', '8', '4', '3', '7', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['3', '7', '7', '8', '1', '3', '7', '/', '1', '1', '2', '0', '0', '0', '0', '0'])), (.str (String.ofList ['7', '8', '5', '9', '3', '7', '1', '/', '1', '2', '2', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['3', '2', '8', '1', '3', '3', '/', '8', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['2', '4', '8', '4', '3', '7', '9', '/', '1', '6', '8', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['3', '7', '5', '0', '0', '3', '/', '2', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['7', '3', '5', '9', '3', '4', '7', '/', '4', '8', '8', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['4', '9', '6', '8', '8', '7', '/', '2', '8', '0', '0', '0', '0', '0'])), (.str (String.ofList ['3', '2', '8', '1', '3', '3', '/', '4', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['2', '6', '7', '1', '8', '9', '1', '/', '8', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['2', '4', '8', '4', '3', '7', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['0'])), (.str (String.ofList ['1', '3', '1', '7', '1', '9', '1', '1', '/', '5', '6', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['0'])), (.str (String.ofList ['1', '2', '4', '2', '2', '1', '1', '9', '/', '5', '6', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['7', '4', '5', '3', '1', '3', '7', '/', '5', '6', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['2', '6', '7', '1', '8', '8', '3', '/', '7', '0', '0', '0', '0', '0', '0']))]) = .ok #[17, 16, 15, 16, 1, 14, 1, 1, 1, 1, 14, 17, 14, 16, 8, 17, 1, 1, 18, 14, 16, 18, 16, 14, 16, 16, 12, 16, 16, 17, 14, 15, 15, 1, 17, 16, 14, 18, 16, 16, 14, 1, 15, 15, 15, 16, 16, 15, 18, 1, 16, 15, 17, 16, 14, 15, 14, 16, 15, 16, 15, 14, 16, 16, 18, 1, 16, 15, 17, 16, 14, 15, 14, 16, 15, 16, 15, 14, 16, 16, 17, 14, 17, 14, 17, 14, 14, 15, 16, 16, 1, 17, 1, 17, 16, 15] := by
  simp

end FieldPreorderProbe
