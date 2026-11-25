import Mathlib.Data.Option.Basic

/-! Structural recovery of the existing successful-parse goal from its tag.
No decidable equality instance is required for either the error or payload type.
This module does not parse or load an archive and proves no closed archive guard.
-/
namespace ImbalancedChen.P2OriginalSaving19ExceptSuccess

theorem eq_ok_getD_of_toOption_isSome {ε : Type u} {α : Type v}
    (p : Except ε α) (fallback : α) (h : p.toOption.isSome = true) :
    p = .ok (p.toOption.getD fallback) := by
  cases p with
  | error e => cases h
  | ok a => rfl

theorem eq_ok_getD_of_isOk {ε : Type u} {α : Type v}
    (p : Except ε α) (fallback : α) (h : p.isOk = true) :
    p = .ok (p.toOption.getD fallback) := by
  cases p with
  | error e => cases h
  | ok a => rfl

theorem isSome_toOption_eq_isOk {ε : Type u} {α : Type v}
    (p : Except ε α) : p.toOption.isSome = p.isOk := by
  cases p <;> rfl

#print axioms eq_ok_getD_of_toOption_isSome
#print axioms eq_ok_getD_of_isOk
#print axioms isSome_toOption_eq_isOk

end ImbalancedChen.P2OriginalSaving19ExceptSuccess
