import ImbalancedChen.P4ACompactBaselineLimit
import ImbalancedChen.P2FirstIntegralSeries
import ImbalancedChen.ActualThirdOriginalLocalCurvature

/-!
SOURCE ONLY / UNCOMPILED.

Exact bridge from the literal ordinary Suzuki root to the original first
integral. The canonical factor is the actual convergent Suzuki source factor;
its numerator recurrence and the genuine lower initial strip supply the
formula on [3,5]. No root enclosure or K bound is assumed or evaluated.

Draft staging:
* same_rho_compact/P4ACompactBaselineLimit.lean.txt ->
  ImbalancedChen/P4ACompactBaselineLimit.lean
* 20261024z-P2/P2FirstIntegralSeries.lean ->
  ImbalancedChen/P2FirstIntegralSeries.lean
* this file -> ImbalancedChen/P4AOrdinaryRootFirstIntegral.lean
-/

namespace ImbalancedChen.P4AOrdinaryRootFirstIntegral20261024zSourceOnly

noncomputable section

open Set MeasureTheory
open MathlibNt.SieveTheory
open OriginalU2CoupledRecurrenceSourceOnly

/-- The first nonconstant upper strip, obtained from the actual source integral
recurrence. The integral includes both original endpoints. -/
theorem upper_numerator_eq_first_integral {s : ℝ}
    (hs3 : 3 ≤ s) (hs5 : s ≤ 5) :
    H s = 1 + ∫ t in (2 : ℝ)..(s - 1), Real.log (t - 1) / t := by
  have hrec : H s - H 3 = ∫ t in (2 : ℝ)..(s - 1), L t / t := by
    simpa only [show (3 : ℝ) - 1 = 2 by norm_num] using
      (H_sub_delayed (x := (3 : ℝ)) (y := s) (by norm_num) hs3)
  have hint : (∫ t in (2 : ℝ)..(s - 1), L t / t) =
      ∫ t in (2 : ℝ)..(s - 1), Real.log (t - 1) / t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by linarith : (2 : ℝ) ≤ s - 1)] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    calc
      L t / t = lower t := by simp [L, ht0]
      _ = Real.log (t - 1) / t :=
        lower_eq_log ht.1 (by linarith [ht.2])
  have hthree : H 3 = 1 := H_eq_one (by norm_num) (by norm_num)
  rw [hint, hthree] at hrec
  linarith only [hrec]

/-- Explicit formula for the genuine canonical upper factor on [3,5]. -/
theorem suzuki_upper_eq_first_integral {s : ℝ}
    (hs3 : 3 ≤ s) (hs5 : s ≤ 5) :
    suzukiContinuousUpperFactor s =
      (2 * Real.exp Real.eulerMascheroniConstant / s) *
        (1 + ∫ t in (2 : ℝ)..(s - 1), Real.log (t - 1) / t) := by
  have hs0 : s ≠ 0 := by linarith
  have ha0 : A ≠ 0 := ne_of_gt A_pos
  have hn := upper_numerator_eq_first_integral hs3 hs5
  have hscaled : s * suzukiContinuousUpperFactor s =
      A * (1 + ∫ t in (2 : ℝ)..(s - 1), Real.log (t - 1) / t) := by
    calc
      _ = A * H s := by
        dsimp only [H, upper]
        field_simp [ha0] <;> ring
      _ = _ := by rw [hn]
  calc
    suzukiContinuousUpperFactor s = (s * suzukiContinuousUpperFactor s) / s := by
      field_simp [hs0] <;> ring
    _ = (A * (1 + ∫ t in (2 : ℝ)..(s - 1), Real.log (t - 1) / t)) / s := by
      rw [hscaled]
    _ = _ := by dsimp only [A]; ring

/-- The two exponential amplitudes cancel before any integral enclosure is used. -/
theorem normalized_upper_eq_constant_add_integral {beta r : ℝ}
    (hb : 0 < beta) (hr : 0 < r)
    (hs3 : 3 ≤ beta / r) (hs5 : beta / r ≤ 5) :
    (2 * Real.exp (-Real.eulerMascheroniConstant) / r) *
        suzukiContinuousUpperFactor (beta / r) =
      4 / beta + (4 / beta) *
        ∫ t in (2 : ℝ)..(beta / r - 1), Real.log (t - 1) / t := by
  have hcoeff :
      (2 * Real.exp (-Real.eulerMascheroniConstant) / r) *
          (2 * Real.exp Real.eulerMascheroniConstant / (beta / r)) = 4 / beta := by
    rw [Real.exp_neg]
    field_simp [ne_of_gt hr, ne_of_gt hb, Real.exp_ne_zero] <;> ring
  rw [suzuki_upper_eq_first_integral hs3 hs5, ← mul_assoc, hcoeff]
  ring

theorem original_ratio_in_first_upper_strip :
    3 ≤ thirdPrefixTheta / thirdPrefixRho ∧
      thirdPrefixTheta / thirdPrefixRho ≤ 5 := by
  norm_num [thirdPrefixTheta, thirdPrefixRho]

/-- Exact original normalization: the same rho, Theta, and full U1 integral. -/
theorem originalOrdinaryRoot_eq_constant_add_originalFirstIntegral :
    P4ASameRhoCompact.originalOrdinaryRoot =
      4 / thirdPrefixTheta + P2FirstIntegralSeriesSourceOnly.originalFirstIntegral := by
  have h := normalized_upper_eq_constant_add_integral
    (beta := thirdPrefixTheta) (r := thirdPrefixRho)
    (by norm_num [thirdPrefixTheta]) (by norm_num [thirdPrefixRho])
    original_ratio_in_first_upper_strip.1 original_ratio_in_first_upper_strip.2
  simpa only [P4ASameRhoCompact.originalOrdinaryRoot,
    P2FirstIntegralSeriesSourceOnly.originalFirstIntegral,
    P2FirstIntegralSeriesSourceOnly.theta, P2FirstIntegralSeriesSourceOnly.rho,
    P2FirstIntegralSeriesSourceOnly.stop, P2FirstIntegralSeriesSourceOnly.kernel,
    thirdPrefixTheta, thirdPrefixRho] using h

/-- Convenient literal form of the same exact identity. -/
theorem originalOrdinaryRoot_eq_literal_constant_add_U1 :
    P4ASameRhoCompact.originalOrdinaryRoot =
      4 / (299 / 500 : ℝ) + P2FirstIntegralSeriesSourceOnly.originalFirstIntegral := by
  simpa only [thirdPrefixTheta] using
    originalOrdinaryRoot_eq_constant_add_originalFirstIntegral

end

end ImbalancedChen.P4AOrdinaryRootFirstIntegral20261024zSourceOnly
