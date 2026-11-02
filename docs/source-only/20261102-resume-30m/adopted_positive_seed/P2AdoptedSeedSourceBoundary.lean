import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

This is obstruction evidence, not an adopted-seed supplier.  In the actual
Wu source, `wuSourceBox`, `wuBoxPhi`, `wuImprovementComparison`, and the
Gamma20/21 unit receiver all use Q=N^(1/2-delta).  The enhanced stable-prefix
seed has physical Q=N^nu with nu>1/2.  The following strict inequalities
rule out an identity of those levels, residuals, cutoffs, and true alpha.

The final coefficient comparison also rules out obtaining the adopted
2327/100000 estimate merely by cutoff monotonicity from the weaker Wu
1/5000 estimate.  It compares the literal reciprocal-log factors in the
same positive marked normalization.  It does NOT show that the adopted
estimate is false, and does NOT assert an enhanced source-count bound.

No source gain, seed, switched K estimate, PP estimate, finite certificate
truth, or endpoint is an assumption or conclusion.  There is no recurrence.
The full adopted-seed target, including its enhanced source gains, is OPEN.
-/

namespace ImbalancedChen.P2AdoptedSeedSourceBoundary

noncomputable section

/-- The two actual total levels cannot be equal on the enhanced branch. -/
theorem enhanced_level_gt_Wu {N : ℕ} {nu delta : ℝ}
    (hN : 1 < N) (hnu : 1/2 < nu) (hdelta : 0 < delta) :
    (N : ℝ) ^ (1/2-delta) < (N : ℝ) ^ nu := by
  apply Real.rpow_lt_rpow_of_exponent_lt
  · exact_mod_cast hN
  · linarith

theorem enhanced_level_ne_Wu {N : ℕ} {nu delta : ℝ}
    (hN : 1 < N) (hnu : 1/2 < nu) (hdelta : 0 < delta) :
    (N : ℝ) ^ nu ≠ (N : ℝ) ^ (1/2-delta) :=
  ne_of_gt (enhanced_level_gt_Wu hN hnu hdelta)

/-- Dividing by the same actual prefix does not remove the mismatch. -/
theorem enhanced_residual_gt_Wu {N d : ℕ} {nu delta : ℝ}
    (hN : 1 < N) (hd : 0 < d) (hnu : 1/2 < nu) (hdelta : 0 < delta) :
    (N : ℝ) ^ (1/2-delta) / d < (N : ℝ) ^ nu / d := by
  exact div_lt_div_of_pos_right (enhanced_level_gt_Wu hN hnu hdelta)
    (Nat.cast_pos.mpr hd)

/-- At the same positive argument, the physical cutoffs are different. -/
theorem enhanced_cutoff_gt_Wu {N d : ℕ} {nu delta s : ℝ}
    (hN : 1 < N) (hd : 0 < d) (hnu : 1/2 < nu)
    (hdelta : 0 < delta) (hs : 0 < s) :
    ((N : ℝ) ^ (1/2-delta) / d) ^ (1/s) <
      ((N : ℝ) ^ nu / d) ^ (1/s) := by
  apply Real.rpow_lt_rpow
  · exact div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _) (Nat.cast_nonneg d)
  · exact enhanced_residual_gt_Wu hN hd hnu hdelta
  · exact one_div_pos.mpr hs

/-- Changing total level changes the real rough argument at the SAME
prefix.  This is the ratio in omega3XPhi, not an alpha reset to two. -/
theorem true_alpha_changes_with_level {N d : ℕ} {nu delta : ℝ}
    (hN : 1 < N) (hd : 0 < d) (hnu : 1/2 < nu) (hdelta : 0 < delta)
    (hres : 1 < (N : ℝ) ^ (1/2-delta) / d) (hquot : 1 < (N : ℝ) / d) :
    Real.log ((N : ℝ) / d) / Real.log ((N : ℝ) ^ nu / d) <
      Real.log ((N : ℝ) / d) / Real.log ((N : ℝ) ^ (1/2-delta) / d) := by
  have hR := enhanced_residual_gt_Wu hN hd hnu hdelta
  have hlog := Real.log_lt_log (by linarith : 0 < (N : ℝ) ^ (1/2-delta) / d) hR
  have hlo := Real.log_pos hres
  have hhi := Real.log_pos (hres.trans hR)
  apply (div_lt_div_iff₀ hhi hlo).2
  exact mul_lt_mul_of_pos_left hlog (Real.log_pos hquot)

/-- Even a cutoff comparison would leave the Wu reciprocal-log upper
coefficient strictly ABOVE the desired adopted-seed coefficient.  The
positive common factors 4*li(N)*sigma(d)*C(d*N)/phi(d) are unchanged.
This theorem asserts no bound on either count. -/
theorem Wu_coefficient_exceeds_adopted {N d : ℕ} {nu delta : ℝ}
    (hN : 1 < N) (hd : 0 < d) (hnu : 1/2 < nu) (hdelta : 0 < delta)
    (hres : 1 < (N : ℝ) ^ (1/2-delta) / d) :
    (1-2327/100000 : ℝ) / Real.log ((N : ℝ) ^ nu / d) <
      (1-1/5000 : ℝ) / Real.log ((N : ℝ) ^ (1/2-delta) / d) := by
  have hR := enhanced_residual_gt_Wu hN hd hnu hdelta
  have hlog := Real.log_lt_log (by linarith : 0 < (N : ℝ) ^ (1/2-delta) / d) hR
  have hlo := Real.log_pos hres
  calc
    (1-2327/100000 : ℝ) / Real.log ((N : ℝ) ^ nu / d) ≤
        (1-2327/100000 : ℝ) / Real.log ((N : ℝ) ^ (1/2-delta) / d) :=
      div_le_div_of_nonneg_left (by norm_num) hlo hlog.le
    _ < (1-1/5000 : ℝ) / Real.log ((N : ℝ) ^ (1/2-delta) / d) :=
      div_lt_div_of_pos_right (by norm_num) hlo

/-- A nonempty real exponent chamber of the original enhanced geometric
conditions: one old slot, a strict full square, largest-prime cap, stable
ceiling and seed comparison.  This is NOT an arithmetic prime-box
existence or a complete factorization/distribution licence. -/
theorem enhanced_geometric_chamber :
    (1/2 : ℝ) < 11/20 ∧ (11/20 : ℝ) < 153/256 ∧
    (0 : ℝ) < 19/100 ∧ (19/100 : ℝ) < 25/128 ∧
    (11/20 : ℝ) = 19/100+9/25 ∧
    (2*(19/100) : ℝ) < 11/20 ∧
    (11/20 : ℝ) < (1+19/100)/2 ∧
    (0 : ℝ) < 9/50 ∧ (9/50 : ℝ) < 19/100 ∧
    ((9/25)/(11/5) : ℝ) < 9/50 ∧
    ((1-19/100)/(9/25) : ℝ) = 9/4 ∧ (2 : ℝ) < 9/4 := by
  norm_num

end
end ImbalancedChen.P2AdoptedSeedSourceBoundary
