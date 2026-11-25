import Lean

namespace FieldComposeProbe

theorem ok_bind (a : Nat) (f : Nat → Except String Nat) :
    ((Except.ok a : Except String Nat) >>= f) = f a := by
  simp

theorem ok_map (a : Nat) (f : Nat → Nat) :
    f <$> (Except.ok a : Except String Nat) = .ok (f a) := by
  simp

theorem array_two (f : Nat → Except String Nat) (a b x y : Nat)
    (ha : f a = .ok x) (hb : f b = .ok y) :
    [a, b].toArray.mapM f = .ok #[x, y] := by
  simp [ha, hb]

structure Record where
  first : Nat
  numbers : Array Nat
  label : String

def decodeRecord (p : Except String Nat) (q : Except String (Array Nat))
    (r : Except String String) : Except String Record := do
  return { first := ← p, numbers := ← q, label := ← r }

theorem record_compose (p : Except String Nat) (q : Except String (Array Nat))
    (r : Except String String) (x : Nat) (xs : Array Nat) (s : String)
    (hp : p = .ok x) (hq : q = .ok xs) (hr : r = .ok s) :
    decodeRecord p q r = .ok { first := x, numbers := xs, label := s } := by
  simp [decodeRecord, hp, hq, hr]

end FieldComposeProbe
