import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Tuple.Basic

/-!
Expression-only probe of the three local coordinate equalities.
No project module or propositional supplier is imported or assumed.
This probe carries no project compilation or mathematical acceptance credit.
-/

namespace P27CoordinateMotiveProbe

set_option Elab.async false

abbrev Point := Fin 4 → ℝ
abbrev Point3 := Fin 3 → ℝ
abbrev Point2 := Fin 2 → ℝ

example (t : ℝ) (v : Point3) :
    (Fin.cons t v : Point) 2 = v 1 ∧
      (Fin.cons t v : Point) 3 = v 2 := by
  have h2 : Fin.cons t v 2 = v 1 := rfl
  have h3 : Fin.cons t v 3 = v 2 := rfl
  exact ⟨h2, h3⟩

example (u : ℝ) (v : Point2) :
    (Fin.cons u v : Point3) 2 = v 1 := by
  have h2 : Fin.cons u v 2 = v 1 := rfl
  exact h2

end P27CoordinateMotiveProbe
