import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# P3 real exceptional parameter and threshold transport

Source-only candidate, 2026-10-24. This file has not been compiled.
The lower bound on `lambda` is an explicit real inequality. No spectral
gap theorem, automorphic object, or spectral mean estimate is asserted.
-/

namespace ImbalancedChen.P3ZExceptionalParameter

noncomputable section

/-- The doubled exceptional spectral parameter, extended by zero to the
regular range. -/
def tau (lambda : ℝ) : ℝ :=
  2 * Real.sqrt (max ((1 : ℝ) / 4 - lambda) 0)

theorem continuous_tau : Continuous tau := by
  unfold tau
  fun_prop

theorem tau_nonneg (lambda : ℝ) : 0 ≤ tau lambda := by
  unfold tau
  exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)

theorem tau_sq (lambda : ℝ) :
    tau lambda ^ 2 = 4 * max ((1 : ℝ) / 4 - lambda) 0 := by
  unfold tau
  calc
    (2 * Real.sqrt (max ((1 : ℝ) / 4 - lambda) 0)) ^ 2 =
        4 * Real.sqrt (max ((1 : ℝ) / 4 - lambda) 0) ^ 2 := by ring
    _ = 4 * max ((1 : ℝ) / 4 - lambda) 0 := by
      rw [Real.sq_sqrt (le_max_right _ _)]

theorem tau_eq_zero_of_regular {lambda : ℝ} (hregular : 1 / 4 ≤ lambda) :
    tau lambda = 0 := by
  unfold tau
  rw [max_eq_right (by linarith)]
  simp

theorem tau_sq_of_exceptional {lambda : ℝ}
    (hexceptional : lambda < 1 / 4) :
    tau lambda ^ 2 = 1 - 4 * lambda := by
  rw [tau_sq, max_eq_left (by linarith)]
  ring

theorem tau_pos_of_exceptional {lambda : ℝ}
    (hexceptional : lambda < 1 / 4) : 0 < tau lambda := by
  unfold tau
  apply mul_pos (by norm_num)
  apply Real.sqrt_pos.mpr
  exact lt_of_lt_of_le (by linarith) (le_max_left _ _)

theorem tau_eq_zero_iff_regular (lambda : ℝ) :
    tau lambda = 0 ↔ 1 / 4 ≤ lambda := by
  constructor
  · intro hzero
    by_contra hregular
    have hpos := tau_pos_of_exceptional (lt_of_not_ge hregular)
    linarith
  · exact tau_eq_zero_of_regular

/-- This is only the rational arithmetic relating the two normalizations. -/
theorem spectral_lower_bound_identity :
    (975 : ℝ) / 4096 = 1 / 4 - ((7 : ℝ) / 64) ^ 2 := by
  norm_num

/-- Conditional conversion of a supplied eigenvalue lower bound. The
arithmetic statement does not supply the eigenvalue lower bound itself. -/
theorem tau_le_seven_thirtyseconds {lambda : ℝ}
    (hlower : (975 : ℝ) / 4096 ≤ lambda) :
    tau lambda ≤ (7 : ℝ) / 32 := by
  have hradicand : max ((1 : ℝ) / 4 - lambda) 0 ≤ ((7 : ℝ) / 64) ^ 2 := by
    apply max_le
    · linarith
    · norm_num
  have hsqrt : Real.sqrt (max ((1 : ℝ) / 4 - lambda) 0) ≤ (7 : ℝ) / 64 := by
    exact Real.sqrt_le_iff.mpr ⟨by norm_num, hradicand⟩
  unfold tau
  linarith

theorem tau_le_one {lambda : ℝ} (hlower : 0 ≤ lambda) : tau lambda ≤ 1 := by
  have hradicand : max ((1 : ℝ) / 4 - lambda) 0 ≤ ((1 : ℝ) / 2) ^ 2 := by
    apply max_le
    · linarith
    · norm_num
  have hsqrt : Real.sqrt (max ((1 : ℝ) / 4 - lambda) 0) ≤ (1 : ℝ) / 2 := by
    exact Real.sqrt_le_iff.mpr ⟨by norm_num, hradicand⟩
  unfold tau
  linarith

theorem exceptional_parameter_bounds {lambda : ℝ}
    (hlower : 0 ≤ lambda) (hexceptional : lambda < 1 / 4) :
    tau lambda ^ 2 = 1 - 4 * lambda ∧ 0 ≤ tau lambda ∧ tau lambda ≤ 1 := by
  exact ⟨tau_sq_of_exceptional hexceptional, tau_nonneg lambda, tau_le_one hlower⟩

/-- Transport an arbitrary positive weight to a positive threshold. This is
the elementary real-power step used before an exceptional mean estimate. -/
theorem rpow_le_threshold_multiplier {W X exponent cap : ℝ}
    (hW : 0 < W) (hX : 0 < X)
    (hexponent : 0 ≤ exponent) (hcap : exponent ≤ cap) :
    W ^ exponent ≤ max 1 ((W / X) ^ cap) * X ^ exponent := by
  have hratio_nonneg : 0 ≤ W / X := div_nonneg hW.le hX.le
  have hratio : (W / X) ^ exponent ≤ max 1 ((W / X) ^ cap) := by
    by_cases hsmall : W / X ≤ 1
    · exact (Real.rpow_le_one hratio_nonneg hsmall hexponent).trans (le_max_left _ _)
    · exact (Real.rpow_le_rpow_of_exponent_le (le_of_lt (lt_of_not_ge hsmall)) hcap).trans
        (le_max_right _ _)
  have hsplit : (W / X) ^ exponent * X ^ exponent = W ^ exponent := by
    rw [← Real.mul_rpow hratio_nonneg hX.le, div_mul_cancel₀ _ hX.ne']
  calc
    W ^ exponent = (W / X) ^ exponent * X ^ exponent := hsplit.symm
    _ ≤ max 1 ((W / X) ^ cap) * X ^ exponent :=
      mul_le_mul_of_nonneg_right hratio (Real.rpow_nonneg hX.le exponent)

theorem rpow_le_seven_thirtyseconds_threshold {W X exponent : ℝ}
    (hW : 0 < W) (hX : 0 < X)
    (hexponent : 0 ≤ exponent) (hcap : exponent ≤ (7 : ℝ) / 32) :
    W ^ exponent ≤ max 1 ((W / X) ^ ((7 : ℝ) / 32)) * X ^ exponent := by
  exact rpow_le_threshold_multiplier hW hX hexponent hcap

/-- The conditional lambda-to-weight bridge, ready for a separately proved
Theorem J mean bound at the threshold `X`. -/
theorem tau_rpow_le_threshold {W X lambda : ℝ}
    (hW : 0 < W) (hX : 0 < X)
    (hlower : (975 : ℝ) / 4096 ≤ lambda) :
    W ^ tau lambda ≤
      max 1 ((W / X) ^ ((7 : ℝ) / 32)) * X ^ tau lambda := by
  exact rpow_le_seven_thirtyseconds_threshold hW hX (tau_nonneg lambda)
    (tau_le_seven_thirtyseconds hlower)

end

end ImbalancedChen.P3ZExceptionalParameter
