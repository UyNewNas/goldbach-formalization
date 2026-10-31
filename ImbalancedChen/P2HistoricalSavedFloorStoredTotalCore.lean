import ImbalancedChen.P2HistoricalSavedFloorRowType
import ImbalancedChen.Certificates.PairedV2FullMask
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.OfFn

namespace ImbalancedChen.P2HistoricalSavedFloorStoredTotal
open P2HistoricalSavedFloorRowsBinder
open scoped BigOperators
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/-- Integer version of the existing natural-sum list bridge; same getD convention. -/
theorem sum_getD_eq_map (xs : List FrozenSavedRow) (f : FrozenSavedRow → ℤ) :
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

end ImbalancedChen.P2HistoricalSavedFloorStoredTotal
