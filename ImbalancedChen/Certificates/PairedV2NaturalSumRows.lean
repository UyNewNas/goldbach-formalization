import ImbalancedChen.Certificates.PairedV2FullCertificateData
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.OfFn

/-! The finite-row/list bridge does not evaluate numerical endpoints.
The length equality rules out the fallback branch of `getD` for every adopted
row. The existing `Row` sigma type still determines exact once-only coverage. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums

open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem approximation_lengths : ∀ i : Fin 186,
    (approximations i).length = 512 - firstU i := by
  decide +kernel

theorem sum_getD_eq_map (xs : List Approximation) (f : Approximation → ℕ) :
    (∑ j : Fin xs.length, f (xs.getD j.val default)) = (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [Fin.sum_univ_succ]
    change f x + (∑ j : Fin xs.length, f (xs.getD j.val default)) =
      f x + (xs.map f).sum
    rw [ih]

theorem strip_sum_eq_map (i : Fin 186) (f : Approximation → ℕ) :
    (∑ j : Fin (512 - firstU i), f (approximation ⟨i, j⟩)) =
      ((approximations i).map f).sum := by
  change (∑ j : Fin (512 - firstU i),
    f ((approximations i).getD j.val default)) = _
  simpa only [approximation_lengths i] using sum_getD_eq_map (approximations i) f

theorem sum_rows_eq_list (f : Approximation → ℕ) :
    (∑ r : Row, f (approximation r)) =
      ((List.ofFn approximations).map (fun xs => (xs.map f).sum)).sum := by
  rw [Fintype.sum_sigma]
  simp_rw [strip_sum_eq_map]
  rw [← List.sum_ofFn, List.ofFn_comp']

end ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums
