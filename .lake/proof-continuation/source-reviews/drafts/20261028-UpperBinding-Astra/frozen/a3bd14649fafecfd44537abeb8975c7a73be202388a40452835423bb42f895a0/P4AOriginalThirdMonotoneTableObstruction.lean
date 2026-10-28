import ImbalancedChen.HistoricalPrefixCertificate
import ImbalancedChen.P1ActualCoarseLevelCeiling

-- SOURCE ONLY / UNCOMPILED_ZERO_CREDIT / NOT ROOT ACCEPTED.
-- This rejects one incorrect interface, not the original construction.
-- Original third activation lowers Theta to Gamma. The generic historical
-- table's levelCheck instead requires old <= cap3. Subsequent fourth/fifth
-- increases must start from the original third policy, not this comparison.

namespace ImbalancedChen.P4AOriginalThirdMonotoneTableObstruction

noncomputable section
open HistoricalThirdCoarse

theorem original_third_cannot_pass_monotone_table
    (e chi : ℝ) (he : 0 ≤ e) (D : HistoricalPrefixCapData)
    (j : Cell D.m) (hj : j ∈ cells e chi D.m) (hstored : j ∈ D.cells3)
    (hold : (D.old : ℝ) = initial e)
    (hthird : (D.cap3 j : ℝ) = levelExponent e (box D.m j)) :
    D.levelCheck ≠ true := by
  intro hcheck
  have hmonotone : (D.old : ℝ) ≤ (D.cap3 j : ℝ) := by
    exact_mod_cast (D.levelCheck_sound hcheck).1 j hstored
  rw [hold, hthird] at hmonotone
  exact (not_le_of_gt
    (P1ActualCoarseLevelCeiling.selected_levelExponent_lt_initial
      e chi he D.m j hj)) hmonotone

end
end ImbalancedChen.P4AOriginalThirdMonotoneTableObstruction
