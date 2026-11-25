import Lean

/- Diagnostic only: exact small SourceJson scalar/array definitions, with a Nat-valued
   stand-in for rational decoding. No Mathlib imports and no production theorem. -/
namespace FieldPreorderProbe
noncomputable section
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
theorem token000_decoded : token (String.ofList ['2', '7', '6', '5', '6', '7', '7', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']) = .ok 17 := by rfl
private theorem token000_literal : token "2765677/108000000" = .ok 17 := token000_decoded
theorem token001_decoded : token (String.ofList ['6', '6', '1', '3', '3', '6', '1', '/', '8', '4', '0', '0', '0', '0', '0', '0']) = .ok 16 := by rfl
private theorem token001_literal : token "6613361/84000000" = .ok 16 := token001_decoded
theorem token002_decoded : token (String.ofList ['5', '2', '2', '5', '8', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']) = .ok 15 := by rfl
private theorem token002_literal : token "522581/24000000" = .ok 15 := token002_decoded
theorem token003_decoded : token (String.ofList ['2', '4', '8', '4', '4', '9', '1', '/', '4', '2', '0', '0', '0', '0', '0', '0']) = .ok 16 := by rfl
private theorem token003_literal : token "2484491/42000000" = .ok 16 := token003_decoded
theorem token004_decoded : token (String.ofList ['0']) = .ok 1 := by rfl
private theorem token004_literal : token "0" = .ok 1 := token004_decoded
theorem token005_decoded : token (String.ofList ['1', '0', '9', '3', '8', '3', '/', '2', '0', '0', '0', '0', '0', '0']) = .ok 14 := by rfl
private theorem token005_literal : token "109383/2000000" = .ok 14 := token005_decoded
theorem token006_decoded : token (String.ofList ['7', '9', '6', '8', '7', '9', '/', '9', '0', '0', '0', '0', '0', '0']) = .ok 14 := by rfl
private theorem token006_literal : token "796879/9000000" = .ok 14 := token006_decoded
theorem token007_decoded : token (String.ofList ['3', '9', '8', '4', '3', '0', '7', '/', '1', '2', '2', '0', '0', '0', '0', '0', '0']) = .ok 17 := by rfl
private theorem token007_literal : token "3984307/122000000" = .ok 17 := token007_decoded
theorem token008_decoded : token (String.ofList ['2', '8', '1', '2', '6', '3', '/', '3', '0', '0', '0', '0', '0', '0']) = .ok 14 := by rfl
private theorem token008_literal : token "281263/3000000" = .ok 14 := token008_decoded
theorem token009_decoded : token (String.ofList ['2', '0', '1', '5', '8', '1', '3', '/', '5', '4', '0', '0', '0', '0', '0', '0']) = .ok 16 := by rfl
private theorem token009_literal : token "2015813/54000000" = .ok 16 := token009_decoded
theorem token010_decoded : token (String.ofList ['1', '/', '7', '5', '0', '0', '0', '0']) = .ok 8 := by rfl
private theorem token010_literal : token "1/750000" = .ok 8 := token010_decoded
theorem token011_decoded : token (String.ofList ['7', '4', '5', '3', '1', '3', '7', '/', '2', '2', '4', '0', '0', '0', '0', '0', '0']) = .ok 17 := by rfl
private theorem token011_literal : token "7453137/224000000" = .ok 17 := token011_decoded
theorem token012_decoded : token (String.ofList ['2', '7', '8', '9', '0', '6', '2', '1', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']) = .ok 18 := by rfl
private theorem token012_literal : token "27890621/108000000" = .ok 18 := token012_decoded
theorem token013_decoded : token (String.ofList ['3', '2', '8', '1', '2', '9', '/', '1', '5', '0', '0', '0', '0', '0']) = .ok 14 := by rfl
private theorem token013_literal : token "328129/1500000" = .ok 14 := token013_decoded
theorem token014_decoded : token (String.ofList ['5', '2', '9', '6', '9', '6', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0']) = .ok 16 := by rfl
private theorem token014_literal : token "5296967/28000000" = .ok 16 := token014_decoded
theorem token015_decoded : token (String.ofList ['3', '2', '7', '9', '6', '5', '4', '3', '/', '2', '4', '4', '0', '0', '0', '0', '0', '0']) = .ok 18 := by rfl
private theorem token015_literal : token "32796543/244000000" = .ok 18 := token015_decoded
theorem token016_decoded : token (String.ofList ['1', '2', '9', '6', '8', '6', '1', '/', '1', '2', '2', '0', '0', '0', '0', '0']) = .ok 16 := by rfl
private theorem token016_literal : token "1296861/12200000" = .ok 16 := token016_decoded
theorem token017_decoded : token (String.ofList ['8', '9', '0', '6', '5', '9', '/', '6', '0', '0', '0', '0', '0', '0']) = .ok 14 := by rfl
private theorem token017_literal : token "890659/6000000" = .ok 14 := token017_decoded
theorem token018_decoded : token (String.ofList ['1', '4', '5', '3', '1', '9', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0']) = .ok 16 := by rfl
private theorem token018_literal : token "1453193/12000000" = .ok 16 := token018_decoded
theorem token019_decoded : token (String.ofList ['1', '5', '4', '6', '9', '0', '9', '/', '1', '2', '0', '0', '0', '0', '0', '0']) = .ok 16 := by rfl
private theorem token019_literal : token "1546909/12000000" = .ok 16 := token019_decoded
theorem token020_decoded : token (String.ofList ['3', '8', '0', '8', '7', '/', '3', '7', '5', '0', '0', '0']) = .ok 12 := by rfl
private theorem token020_literal : token "38087/375000" = .ok 12 := token020_decoded
theorem token021_decoded : token (String.ofList ['2', '7', '6', '5', '6', '7', '7', '/', '2', '7', '0', '0', '0', '0', '0', '0']) = .ok 16 := by rfl
private theorem token021_literal : token "2765677/27000000" = .ok 16 := token021_decoded
theorem token022_decoded : token (String.ofList ['2', '7', '6', '5', '6', '7', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0']) = .ok 16 := by rfl
private theorem token022_literal : token "2765677/36000000" = .ok 16 := token022_decoded
theorem token023_decoded : token (String.ofList ['7', '5', '4', '7', '1', '6', '7', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']) = .ok 17 := by rfl
private theorem token023_literal : token "7547167/108000000" = .ok 17 := token023_decoded
theorem token024_decoded : token (String.ofList ['1', '5', '9', '3', '8', '3', '/', '3', '6', '0', '0', '0', '0', '0']) = .ok 14 := by rfl
private theorem token024_literal : token "159383/3600000" = .ok 14 := token024_decoded
theorem token025_decoded : token (String.ofList ['7', '9', '6', '9', '2', '7', '/', '1', '8', '0', '0', '0', '0', '0', '0']) = .ok 15 := by rfl
private theorem token025_literal : token "796927/18000000" = .ok 15 := token025_decoded
theorem token026_decoded : token (String.ofList ['5', '3', '5', '9', '2', '5', '1', '/', '4', '8', '8', '0', '0', '0', '0', '0', '0']) = .ok 17 := by rfl
private theorem token026_literal : token "5359251/488000000" = .ok 17 := token026_decoded
theorem token027_decoded : token (String.ofList ['2', '4', '8', '4', '3', '7', '9', '/', '5', '6', '0', '0', '0', '0', '0', '0']) = .ok 16 := by rfl
private theorem token027_literal : token "2484379/56000000" = .ok 16 := token027_decoded
theorem token028_decoded : token (String.ofList ['2', '3', '4', '3', '7', '9', '/', '2', '4', '0', '0', '0', '0', '0']) = .ok 14 := by rfl
private theorem token028_literal : token "234379/2400000" = .ok 14 := token028_decoded
theorem token029_decoded : token (String.ofList ['2', '2', '0', '7', '8', '0', '4', '1', '/', '4', '8', '8', '0', '0', '0', '0', '0', '0']) = .ok 18 := by rfl
private theorem token029_literal : token "22078041/488000000" = .ok 18 := token029_decoded
theorem token030_decoded : token (String.ofList ['2', '4', '8', '4', '4', '9', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']) = .ok 16 := by rfl
private theorem token030_literal : token "2484491/28000000" = .ok 16 := token030_decoded
theorem token031_decoded : token (String.ofList ['5', '8', '5', '9', '4', '2', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0']) = .ok 16 := by rfl
private theorem token031_literal : token "5859427/24000000" = .ok 16 := token031_decoded
theorem token032_decoded : token (String.ofList ['3', '6', '5', '6', '2', '9', '/', '4', '8', '0', '0', '0', '0', '0']) = .ok 14 := by rfl
private theorem token032_literal : token "365629/4800000" = .ok 14 := token032_decoded
theorem token033_decoded : token (String.ofList ['3', '2', '8', '1', '3', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0']) = .ok 15 := by rfl
private theorem token033_literal : token "328133/12000000" = .ok 15 := token033_decoded
theorem token034_decoded : token (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '8', '0', '0', '0', '0', '0', '0']) = .ok 15 := by rfl
private theorem token034_literal : token "1171879/8000000" = .ok 15 := token034_decoded
theorem token035_decoded : token (String.ofList ['7', '4', '5', '3', '3', '6', '1', '/', '5', '6', '0', '0', '0', '0', '0', '0']) = .ok 16 := by rfl
private theorem token035_literal : token "7453361/56000000" = .ok 16 := token035_decoded
theorem token036_decoded : token (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '4', '0', '0', '0', '0', '0', '0']) = .ok 15 := by rfl
private theorem token036_literal : token "1171879/4000000" = .ok 15 := token036_decoded
theorem token037_decoded : token (String.ofList ['3', '8', '7', '9', '6', '8', '3', '1', '/', '4', '8', '8', '0', '0', '0', '0', '0', '0']) = .ok 18 := by rfl
private theorem token037_literal : token "38796831/488000000" = .ok 18 := token037_decoded
theorem token038_decoded : token (String.ofList ['2', '4', '8', '4', '3', '7', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0']) = .ok 16 := by rfl
private theorem token038_literal : token "2484379/84000000" = .ok 16 := token038_decoded
theorem token039_decoded : token (String.ofList ['7', '3', '5', '9', '3', '4', '7', '/', '2', '4', '4', '0', '0', '0', '0', '0', '0']) = .ok 17 := by rfl
private theorem token039_literal : token "7359347/244000000" = .ok 17 := token039_decoded
theorem token040_decoded : token (String.ofList ['3', '2', '8', '1', '3', '3', '/', '8', '0', '0', '0', '0', '0', '0']) = .ok 14 := by rfl
private theorem token040_literal : token "328133/8000000" = .ok 14 := token040_decoded
theorem token041_decoded : token (String.ofList ['1', '2', '5', '0', '0', '1', '/', '2', '0', '0', '0', '0', '0', '0']) = .ok 14 := by rfl
private theorem token041_literal : token "125001/2000000" = .ok 14 := token041_decoded
theorem token042_decoded : token (String.ofList ['3', '2', '8', '1', '3', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0']) = .ok 15 := by rfl
private theorem token042_literal : token "328133/24000000" = .ok 15 := token042_decoded
theorem token043_decoded : token (String.ofList ['2', '6', '7', '1', '8', '8', '3', '/', '1', '4', '0', '0', '0', '0', '0', '0']) = .ok 16 := by rfl
private theorem token043_literal : token "2671883/14000000" = .ok 16 := token043_decoded
theorem token044_decoded : token (String.ofList ['4', '9', '6', '8', '8', '7', '/', '2', '8', '0', '0', '0', '0', '0']) = .ok 14 := by rfl
private theorem token044_literal : token "496887/2800000" = .ok 14 := token044_decoded
theorem token045_decoded : token (String.ofList ['2', '4', '8', '4', '3', '7', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0']) = .ok 16 := by rfl
private theorem token045_literal : token "2484379/28000000" = .ok 16 := token045_decoded
theorem token046_decoded : token (String.ofList ['3', '7', '7', '8', '1', '3', '7', '/', '1', '1', '2', '0', '0', '0', '0', '0']) = .ok 16 := by rfl
private theorem token046_literal : token "3778137/11200000" = .ok 16 := token046_decoded
theorem token047_decoded : token (String.ofList ['7', '8', '5', '9', '3', '7', '1', '/', '1', '2', '2', '0', '0', '0', '0', '0', '0']) = .ok 17 := by rfl
private theorem token047_literal : token "7859371/122000000" = .ok 17 := token047_decoded
theorem token048_decoded : token (String.ofList ['2', '4', '8', '4', '3', '7', '9', '/', '1', '6', '8', '0', '0', '0', '0', '0', '0']) = .ok 17 := by rfl
private theorem token048_literal : token "2484379/168000000" = .ok 17 := token048_decoded
theorem token049_decoded : token (String.ofList ['3', '7', '5', '0', '0', '3', '/', '2', '0', '0', '0', '0', '0', '0']) = .ok 14 := by rfl
private theorem token049_literal : token "375003/2000000" = .ok 14 := token049_decoded
theorem token050_decoded : token (String.ofList ['7', '3', '5', '9', '3', '4', '7', '/', '4', '8', '8', '0', '0', '0', '0', '0', '0']) = .ok 17 := by rfl
private theorem token050_literal : token "7359347/488000000" = .ok 17 := token050_decoded
theorem token051_decoded : token (String.ofList ['3', '2', '8', '1', '3', '3', '/', '4', '0', '0', '0', '0', '0', '0']) = .ok 14 := by rfl
private theorem token051_literal : token "328133/4000000" = .ok 14 := token051_decoded
theorem token052_decoded : token (String.ofList ['2', '6', '7', '1', '8', '9', '1', '/', '8', '0', '0', '0', '0', '0', '0']) = .ok 15 := by rfl
private theorem token052_literal : token "2671891/8000000" = .ok 15 := token052_decoded
theorem token053_decoded : token (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0']) = .ok 16 := by rfl
private theorem token053_literal : token "1171879/24000000" = .ok 16 := token053_decoded
theorem token054_decoded : token (String.ofList ['1', '3', '1', '7', '1', '9', '1', '1', '/', '5', '6', '0', '0', '0', '0', '0', '0']) = .ok 17 := by rfl
private theorem token054_literal : token "13171911/56000000" = .ok 17 := token054_decoded
theorem token055_decoded : token (String.ofList ['1', '2', '4', '2', '2', '1', '1', '9', '/', '5', '6', '0', '0', '0', '0', '0', '0']) = .ok 17 := by rfl
private theorem token055_literal : token "12422119/56000000" = .ok 17 := token055_decoded
theorem token056_decoded : token (String.ofList ['7', '4', '5', '3', '1', '3', '7', '/', '5', '6', '0', '0', '0', '0', '0', '0']) = .ok 16 := by rfl
private theorem token056_literal : token "7453137/56000000" = .ok 16 := token056_decoded
theorem token057_decoded : token (String.ofList ['2', '6', '7', '1', '8', '8', '3', '/', '7', '0', '0', '0', '0', '0', '0']) = .ok 15 := by rfl
private theorem token057_literal : token "2671883/7000000" = .ok 15 := token057_decoded
attribute [local simp] token000_literal token001_literal token002_literal token003_literal token004_literal token005_literal token006_literal token007_literal token008_literal token009_literal token010_literal token011_literal token012_literal token013_literal token014_literal token015_literal token016_literal token017_literal token018_literal token019_literal token020_literal token021_literal token022_literal token023_literal token024_literal token025_literal token026_literal token027_literal token028_literal token029_literal token030_literal token031_literal token032_literal token033_literal token034_literal token035_literal token036_literal token037_literal token038_literal token039_literal token040_literal token041_literal token042_literal token043_literal token044_literal token045_literal token046_literal token047_literal token048_literal token049_literal token050_literal token051_literal token052_literal token053_literal token054_literal token055_literal token056_literal token057_literal
theorem minima96 : tokenArray (.arr [(.str (String.ofList ['2', '7', '6', '5', '6', '7', '7', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['6', '6', '1', '3', '3', '6', '1', '/', '8', '4', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['5', '2', '2', '5', '8', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['2', '4', '8', '4', '4', '9', '1', '/', '4', '2', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['0'])), (.str (String.ofList ['1', '0', '9', '3', '8', '3', '/', '2', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['0'])), (.str (String.ofList ['0'])), (.str (String.ofList ['0'])), (.str (String.ofList ['0'])), (.str (String.ofList ['7', '9', '6', '8', '7', '9', '/', '9', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['3', '9', '8', '4', '3', '0', '7', '/', '1', '2', '2', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['2', '8', '1', '2', '6', '3', '/', '3', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['2', '0', '1', '5', '8', '1', '3', '/', '5', '4', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['1', '/', '7', '5', '0', '0', '0', '0'])), (.str (String.ofList ['7', '4', '5', '3', '1', '3', '7', '/', '2', '2', '4', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['0'])), (.str (String.ofList ['0'])), (.str (String.ofList ['2', '7', '8', '9', '0', '6', '2', '1', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['3', '2', '8', '1', '2', '9', '/', '1', '5', '0', '0', '0', '0', '0'])), (.str (String.ofList ['5', '2', '9', '6', '9', '6', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['3', '2', '7', '9', '6', '5', '4', '3', '/', '2', '4', '4', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['1', '2', '9', '6', '8', '6', '1', '/', '1', '2', '2', '0', '0', '0', '0', '0'])), (.str (String.ofList ['8', '9', '0', '6', '5', '9', '/', '6', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['1', '4', '5', '3', '1', '9', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['1', '5', '4', '6', '9', '0', '9', '/', '1', '2', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['3', '8', '0', '8', '7', '/', '3', '7', '5', '0', '0', '0'])), (.str (String.ofList ['2', '7', '6', '5', '6', '7', '7', '/', '2', '7', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['2', '7', '6', '5', '6', '7', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['7', '5', '4', '7', '1', '6', '7', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['1', '5', '9', '3', '8', '3', '/', '3', '6', '0', '0', '0', '0', '0'])), (.str (String.ofList ['7', '9', '6', '9', '2', '7', '/', '1', '8', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['7', '9', '6', '9', '2', '7', '/', '1', '8', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['0'])), (.str (String.ofList ['5', '3', '5', '9', '2', '5', '1', '/', '4', '8', '8', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['2', '4', '8', '4', '3', '7', '9', '/', '5', '6', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['2', '3', '4', '3', '7', '9', '/', '2', '4', '0', '0', '0', '0', '0'])), (.str (String.ofList ['2', '2', '0', '7', '8', '0', '4', '1', '/', '4', '8', '8', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['2', '4', '8', '4', '4', '9', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['5', '8', '5', '9', '4', '2', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['3', '6', '5', '6', '2', '9', '/', '4', '8', '0', '0', '0', '0', '0'])), (.str (String.ofList ['0'])), (.str (String.ofList ['3', '2', '8', '1', '3', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '8', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['3', '2', '8', '1', '3', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['7', '4', '5', '3', '3', '6', '1', '/', '5', '6', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['2', '4', '8', '4', '3', '7', '9', '/', '5', '6', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '4', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['3', '8', '7', '9', '6', '8', '3', '1', '/', '4', '8', '8', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['0'])), (.str (String.ofList ['2', '4', '8', '4', '3', '7', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '8', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['7', '3', '5', '9', '3', '4', '7', '/', '2', '4', '4', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['7', '4', '5', '3', '3', '6', '1', '/', '5', '6', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['3', '2', '8', '1', '3', '3', '/', '8', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '4', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['1', '2', '5', '0', '0', '1', '/', '2', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['2', '4', '8', '4', '3', '7', '9', '/', '5', '6', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['3', '2', '8', '1', '3', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['2', '6', '7', '1', '8', '8', '3', '/', '1', '4', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['3', '2', '8', '1', '3', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['4', '9', '6', '8', '8', '7', '/', '2', '8', '0', '0', '0', '0', '0'])), (.str (String.ofList ['2', '4', '8', '4', '3', '7', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['3', '7', '7', '8', '1', '3', '7', '/', '1', '1', '2', '0', '0', '0', '0', '0'])), (.str (String.ofList ['3', '8', '7', '9', '6', '8', '3', '1', '/', '4', '8', '8', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['0'])), (.str (String.ofList ['2', '4', '8', '4', '3', '7', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '8', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['7', '3', '5', '9', '3', '4', '7', '/', '2', '4', '4', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['7', '4', '5', '3', '3', '6', '1', '/', '5', '6', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['3', '2', '8', '1', '3', '3', '/', '8', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '4', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['1', '2', '5', '0', '0', '1', '/', '2', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['2', '4', '8', '4', '3', '7', '9', '/', '5', '6', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['3', '2', '8', '1', '3', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['2', '6', '7', '1', '8', '8', '3', '/', '1', '4', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['3', '2', '8', '1', '3', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['4', '9', '6', '8', '8', '7', '/', '2', '8', '0', '0', '0', '0', '0'])), (.str (String.ofList ['2', '4', '8', '4', '3', '7', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['3', '7', '7', '8', '1', '3', '7', '/', '1', '1', '2', '0', '0', '0', '0', '0'])), (.str (String.ofList ['7', '8', '5', '9', '3', '7', '1', '/', '1', '2', '2', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['3', '2', '8', '1', '3', '3', '/', '8', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['2', '4', '8', '4', '3', '7', '9', '/', '1', '6', '8', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['3', '7', '5', '0', '0', '3', '/', '2', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['7', '3', '5', '9', '3', '4', '7', '/', '4', '8', '8', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['4', '9', '6', '8', '8', '7', '/', '2', '8', '0', '0', '0', '0', '0'])), (.str (String.ofList ['3', '2', '8', '1', '3', '3', '/', '4', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['2', '6', '7', '1', '8', '9', '1', '/', '8', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['2', '4', '8', '4', '3', '7', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['0'])), (.str (String.ofList ['1', '3', '1', '7', '1', '9', '1', '1', '/', '5', '6', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['0'])), (.str (String.ofList ['1', '2', '4', '2', '2', '1', '1', '9', '/', '5', '6', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['7', '4', '5', '3', '1', '3', '7', '/', '5', '6', '0', '0', '0', '0', '0', '0'])), (.str (String.ofList ['2', '6', '7', '1', '8', '8', '3', '/', '7', '0', '0', '0', '0', '0', '0']))]) = .ok #[17, 16, 15, 16, 1, 14, 1, 1, 1, 1, 14, 17, 14, 16, 8, 17, 1, 1, 18, 14, 16, 18, 16, 14, 16, 16, 12, 16, 16, 17, 14, 15, 15, 1, 17, 16, 14, 18, 16, 16, 14, 1, 15, 15, 15, 16, 16, 15, 18, 1, 16, 15, 17, 16, 14, 15, 14, 16, 15, 16, 15, 14, 16, 16, 18, 1, 16, 15, 17, 16, 14, 15, 14, 16, 15, 16, 15, 14, 16, 16, 17, 14, 17, 14, 17, 14, 14, 15, 16, 16, 1, 17, 1, 17, 16, 15] := by
  simp
end
end FieldPreorderProbe
