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
theorem token_one_decoded : token (String.ofList ['1', '/', '7']) = .ok 3 := by rfl
attribute [local simp] decodeNat_number_ofList token_one_decoded
theorem nat_zero : (Decode.read (.number (String.ofList ['0'])) : Except String Nat) = .ok 0 := by simp
theorem nat_eight : (Decode.read (.number (String.ofList ['8'])) : Except String Nat) = .ok 8 := by simp
theorem nat_array : (Decode.read (.arr [.number (String.ofList ['1']), .number (String.ofList ['8'])]) : Except String (Array Nat)) = .ok #[1,8] := by simp
theorem token_one : tokenArray (.arr [.str (String.ofList ['1','/','7'])]) = .ok #[3] := by simp
end
end FieldPreorderProbe
