import ImbalancedChen.P2SeedOmegaLiteralFibre
import Mathlib.Analysis.Complex.Exponential

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The ORIGINAL c_omega=70893/125000 is an analytic global envelope for the
actual pinned Buchstab function. The initial [2,3] proof uses log(y)<=y-1,
the finite positive exponential Taylor sum, and the original explicit
rational surplus. The actual delay equation propagates this FULL unit
interval to the unbounded tail using the pinned theorem, without any
finite alpha strip, desired omega cap, or final seed inequality as input.
No numerical certificate, evaluator, compiler, or replay was run.
-/

namespace ImbalancedChen.P2SeedOmegaGlobalEnvelope
noncomputable section
open Set LiLiuPrereqBuchstab
open scoped BigOperators
open P2SeedOmegaLiteralFibre (omegaCap)

theorem omegaCap_positive : 0<omegaCap := by norm_num [omegaCap]

/-- The nine explicit Taylor terms in the original analytic proof.
This is a source proof of one rational identity, not a saved PASS receipt. -/
theorem original_exp8_surplus :
    omegaCap*(∑ k ∈ Finset.range 9,omegaCap^k/(Nat.factorial k:ℝ))-1=
      (65111700737847638377192824351410078164698277:ℝ)/
        33378601074218750000000000000000000000000000000000 := by
  norm_num [omegaCap,Finset.sum_range_succ,Nat.factorial]

theorem omegaCap_mul_exp_gt_one : 1<omegaCap*Real.exp omegaCap := by
  have hTaylor := Real.sum_le_exp_of_nonneg omegaCap_positive.le 9
  have hmult := mul_le_mul_of_nonneg_left hTaylor omegaCap_positive.le
  have hsurplus := original_exp8_surplus
  have hpos : (0:ℝ)<
      65111700737847638377192824351410078164698277/
        33378601074218750000000000000000000000000000000000 := by positivity
  linarith only [hmult,hsurplus,hpos]

/-- The logarithmic sign underlying the original sharp envelope is
derived analytically, rather than supplied as a numerical premise. -/
theorem omegaCap_log_slack : 0<Real.log omegaCap+omegaCap := by
  have h := Real.log_pos omegaCap_mul_exp_gt_one
  rw [Real.log_mul omegaCap_positive.ne' (Real.exp_pos omegaCap).ne',Real.log_exp] at h
  exact h

theorem original_log_tangent {v : ℝ} (hv : 0<v) :
    1+Real.log v<omegaCap*(v+1) := by
  have h := Real.log_le_sub_one_of_pos (mul_pos omegaCap_positive hv)
  rw [Real.log_mul omegaCap_positive.ne' hv.ne'] at h
  have hslack := omegaCap_log_slack
  nlinarith only [h,hslack]

/-- Entire starting window, including both closed endpoints. -/
theorem actual_buchstab_first_window {u : ℝ} (hu : u ∈ Icc (2:ℝ) 3) :
    buchstab u≤omegaCap := by
  rw [buchstab_eq_log_div hu.1 hu.2]
  apply (div_le_iff₀ (show 0<u by linarith only [hu.1])).mpr
  have h := original_log_tangent (v:=u-1) (by linarith only [hu.1])
  nlinarith only [h]

/-- Unbounded actual tail: no alpha upper cutoff and no finite starting
certificate assumption. The pinned propagation theorem pays induction. -/
theorem actual_buchstab_global_cap {u : ℝ} (hu : 2≤u) :
    buchstab u≤omegaCap := by
  apply buchstab_upper_on_tail (a:=(2:ℝ)) (by norm_num) _ u hu
  intro v hv
  apply actual_buchstab_first_window
  simpa only [show (2:ℝ)+1=3 by norm_num] using hv

theorem actual_buchstab_original_global_envelope {u : ℝ} (hu : 1≤u) :
    buchstab u≤max (1/u) omegaCap := by
  by_cases htwo : u≤2
  · rw [buchstab_eq_one_div hu htwo]
    exact le_max_left _ _
  · exact (actual_buchstab_global_cap (lt_of_not_ge htwo).le).trans (le_max_right _ _)

end
end ImbalancedChen.P2SeedOmegaGlobalEnvelope
