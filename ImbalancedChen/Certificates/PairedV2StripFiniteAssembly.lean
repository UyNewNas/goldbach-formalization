import Mathlib.Data.Fin.Basic

namespace ImbalancedChen.Certificates.PairedV2.FullMask.StripAssembly

/-- Transport an exhaustive finite predicate without simplifying that predicate. -/
theorem forallFinCast {n m : Nat} (h : n = m) (P : Fin n → Prop)
    (hp : ∀ j : Fin m, P (Fin.cast h.symm j)) : ∀ j : Fin n, P j := by
  intro j
  have hj : Fin.cast h.symm (Fin.cast h j) = j := by
    apply Fin.ext
    rfl
  exact Eq.mp (congrArg P hj) (hp (Fin.cast h j))

/-- Exhaustive disjoint left/right finite concatenation. -/
theorem forallFinAdd {a b : Nat} (P : Fin (a + b) → Prop)
    (hl : ∀ j : Fin a, P (Fin.castAdd b j))
    (hr : ∀ j : Fin b, P (Fin.natAdd a j)) : ∀ j : Fin (a + b), P j := by
  intro j
  exact Fin.addCases (motive := P) hl hr j

/-- Compose concatenation and cardinality transport over an abstract predicate. -/
theorem forallFinCastAdd {n a b : Nat} (h : n = a + b) (P : Fin n → Prop)
    (hl : ∀ j : Fin a, P (Fin.cast h.symm (Fin.castAdd b j)))
    (hr : ∀ j : Fin b, P (Fin.cast h.symm (Fin.natAdd a j))) :
    ∀ j : Fin n, P j :=
  forallFinCast h P
    (forallFinAdd (fun j => P (Fin.cast h.symm j)) hl hr)

end ImbalancedChen.Certificates.PairedV2.FullMask.StripAssembly
