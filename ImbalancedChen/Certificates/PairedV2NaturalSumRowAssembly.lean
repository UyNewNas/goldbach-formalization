import ImbalancedChen.Certificates.PairedV2NaturalSumRows
import ImbalancedChen.Certificates.PairedV2NaturalSumLengths

/-! Original Row/list statements using the separately assembled length theorem.
No dependent 186-case proof or full-witness length reduction occurs here. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums

open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip_sum_eq_map (i : Fin 186) (f : Approximation → ℕ) :
    (∑ j : Fin (512 - firstU i), f (approximation ⟨i, j⟩)) =
      ((approximations i).map f).sum := by
  change (∑ j : Fin (512 - firstU i),
    f ((approximations i).getD j.val default)) = _
  rw [← approximation_lengths i]
  exact sum_getD_eq_map (approximations i) f

theorem sum_rows_eq_list (f : Approximation → ℕ) :
    (∑ r : Row, f (approximation r)) =
      ((List.ofFn approximations).map (fun xs => (xs.map f).sum)).sum := by
  rw [Fintype.sum_sigma]
  simp_rw [strip_sum_eq_map]
  rw [← List.sum_ofFn,
    List.ofFn_comp' approximations (fun xs => (xs.map f).sum)]

end ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums
