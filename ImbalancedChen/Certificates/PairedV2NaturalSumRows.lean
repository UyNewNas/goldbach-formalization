import ImbalancedChen.Certificates.PairedV2FullChecker
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.OfFn

/-! Generic finite list-sum bridge. No certificate-data module is imported. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums

open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem sum_getD_eq_map (xs : List Approximation) (f : Approximation → ℕ) :
    (∑ j : Fin xs.length, f (xs.getD j.val default)) = (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    change (∑ j : Fin (xs.length + 1), f ((x :: xs).getD j.val default)) =
      f x + (xs.map f).sum
    rw [Fin.sum_univ_succ]
    change f x + (∑ j : Fin xs.length, f (xs.getD j.val default)) =
      f x + (xs.map f).sum
    rw [ih]

end ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums
