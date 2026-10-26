import ImbalancedChen.Part3LevelOldformFrickeIdentity
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Genuine zero Fourier mean of the actual completed K series at every
positive integral horizontal dilation. Absolute integration is supplied by
the proved norm-summable actual K terms. The central dslope value is retained.
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-26. -/

noncomputable section
open Set MeasureTheory Complex
open scoped Topology UpperHalfPlane
open ImbalancedChen.Part3ActualRamanujanBesselNormalConvergence
open ImbalancedChen.Part3.CompletedEisensteinReflection20261025a
open ImbalancedChen.Part3.CompletedActualEisensteinIdentity20261025a
open ImbalancedChen.Part3.FiniteLevelEisensteinOldforms20261025a
open ImbalancedChen.Part3.PrimeLevelEisensteinDegeneracy20261025a
open ImbalancedChen.Part3.PrimitiveEisensteinFourierParameterAnalytic

namespace ImbalancedChen.Part3.CompletedEisensteinIntegerMean20261026a

theorem scaledTerm_continuous (n : ℕ) (s : ℂ) (y : ℝ) (k : ℤ) :
    Continuous (fun x : ℝ => fourierBesselTerm n s y ((k : ℝ) * x)) := by
  unfold fourierBesselTerm phase
  fun_prop

theorem scaledTerm_norm (n : ℕ) (s : ℂ) (y : ℝ) (k : ℤ) (x : ℝ) :
    ‖fourierBesselTerm n s y ((k : ℝ) * x)‖ = ‖fourierBesselTerm n s y 0‖ := by
  simp only [fourierBesselTerm, norm_mul, norm_phase, mul_one]

theorem scaledSum_continuous (s : ℂ) {y : ℝ} (hy : 0 < y) (k : ℤ) :
    Continuous (fun x : ℝ => ∑' n, fourierBesselTerm n s y ((k : ℝ) * x)) :=
  continuous_tsum (fun n => scaledTerm_continuous n s y k)
    (fourierBessel_norm_summable s hy 0) (fun n x => (scaledTerm_norm n s y k x).le)

theorem phase_integer_mean (n : ℕ) (hn : 0 < n) (k : ℤ) (hk : k ≠ 0) :
    (∫ x in (0 : ℝ)..1, phase n ((k : ℝ) * x)) = 0 := by
  let c : ℂ := ((n : ℤ) * k : ℤ) * (2 * Real.pi * Complex.I)
  have hc : c ≠ 0 := by
    dsimp [c]
    exact mul_ne_zero (Int.cast_ne_zero.mpr (mul_ne_zero (by exact_mod_cast hn.ne') hk))
      (mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
  have he : (fun x : ℝ => phase n ((k : ℝ) * x)) =
      (fun x : ℝ => Complex.exp (c * x)) := by
    funext x
    unfold phase c
    congr 1
    push_cast
    ring
  rw [he, integral_exp_mul_complex hc]
  simp only [mul_one, mul_zero, Complex.exp_zero]
  rw [show Complex.exp c = 1 from Complex.exp_int_mul_two_pi_mul_I ((n : ℤ) * k)]
  simp

theorem scaledTerm_mean (n : ℕ) (s : ℂ) (y : ℝ) (k : ℤ) (hk : k ≠ 0) :
    (∫ x in (0 : ℝ)..1, fourierBesselTerm n s y ((k : ℝ) * x)) = 0 := by
  unfold fourierBesselTerm
  rw [intervalIntegral.integral_const_mul, phase_integer_mean (n + 1) (by omega) k hk, mul_zero]

/-- True interchange of the actual infinite K series with the unit-interval integral. -/
theorem scaledSum_mean (s : ℂ) {y : ℝ} (hy : 0 < y) (k : ℤ) (hk : k ≠ 0) :
    (∫ x in (0 : ℝ)..1, ∑' n, fourierBesselTerm n s y ((k : ℝ) * x)) = 0 := by
  let F : ℕ → ℝ → ℂ := fun n x => fourierBesselTerm n s y ((k : ℝ) * x)
  have hint : ∀ n, Integrable (F n) (volume.restrict (Ioc (0 : ℝ) 1)) := by
    intro n
    exact ((scaledTerm_continuous n s y k).intervalIntegrable 0 1).1
  have hnorm (n : ℕ) : (∫ x in Ioc (0 : ℝ) 1, ‖F n x‖) =
      ‖fourierBesselTerm n s y 0‖ := by
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    simp only [F, scaledTerm_norm]
    simp
  have hsum : Summable (fun n => ∫ x in Ioc (0 : ℝ) 1, ‖F n x‖) := by
    simpa only [hnorm] using fourierBessel_norm_summable s hy 0
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [← integral_tsum_of_summable_integral_norm hint hsum]
  apply tsum_eq_zero
  intro n
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact scaledTerm_mean n s y k hk

theorem scaledPairSum_eq (s : ℂ) {y : ℝ} (hy : 0 < y) (k : ℤ) (x : ℝ) :
    (∑' n, nonzeroFrequencyPair n s y ((k : ℝ) * x)) =
      (∑' n, fourierBesselTerm n s y ((k : ℝ) * x)) +
      (∑' n, fourierBesselTerm n s y (((-k : ℤ) : ℝ) * x)) := by
  simp only [nonzeroFrequencyPair, Int.cast_neg, neg_mul]
  exact tsum_add (fourierBessel_norm_summable s hy _).of_norm
    (fourierBessel_norm_summable s hy _).of_norm

theorem scaledPairSum_continuous (s : ℂ) {y : ℝ} (hy : 0 < y) (k : ℤ) :
    Continuous (fun x : ℝ => ∑' n, nonzeroFrequencyPair n s y ((k : ℝ) * x)) := by
  simp_rw [scaledPairSum_eq s hy k]
  exact (scaledSum_continuous s hy k).add (scaledSum_continuous s hy (-k))

theorem scaledPairSum_mean (s : ℂ) {y : ℝ} (hy : 0 < y) (k : ℤ) (hk : k ≠ 0) :
    (∫ x in (0 : ℝ)..1, ∑' n, nonzeroFrequencyPair n s y ((k : ℝ) * x)) = 0 := by
  simp_rw [scaledPairSum_eq s hy k]
  rw [intervalIntegral.integral_add
    ((scaledSum_continuous s hy k).intervalIntegrable 0 1)
    ((scaledSum_continuous s hy (-k)).intervalIntegrable 0 1),
    scaledSum_mean s hy k hk, scaledSum_mean s hy (-k) (neg_ne_zero.mpr hk), add_zero]

theorem completedFourier_scaled_continuous (s : ℂ) {y : ℝ} (hy : 0 < y) (k : ℤ) :
    Continuous (fun x : ℝ => completedEisensteinFourier s y ((k : ℝ) * x)) :=
  continuous_const.add (continuous_const.mul (scaledPairSum_continuous s hy k))

/-- Actual completed constant mean, also at the central spectral parameter. -/
theorem completedFourier_integer_mean (s : ℂ) {y : ℝ} (hy : 0 < y)
    (k : ℤ) (hk : k ≠ 0) :
    (∫ x in (0 : ℝ)..1, completedEisensteinFourier s y ((k : ℝ) * x)) =
      completedConstant y s := by
  unfold completedEisensteinFourier
  rw [intervalIntegral.integral_add (continuous_const.intervalIntegrable 0 1)
    ((continuous_const.mul (scaledPairSum_continuous s hy k)).intervalIntegrable 0 1),
    intervalIntegral.integral_const_mul, scaledPairSum_mean s hy k hk]
  simp

theorem completed_integer_dilation_continuous (s : ℂ) (n : ℕ+)
    (y : ℝ) (hy : 0 < y) :
    Continuous (fun x : ℝ => completedActualEisenstein s (pnatDilate n (horizontalPoint y hy x))) := by
  have hny : 0 < (n : ℝ) * y := mul_pos (by exact_mod_cast n.pos) hy
  simpa [completedActualEisenstein, pnatDilate, dilate, horizontalPoint,
    Complex.mul_re, Complex.mul_im] using
      completedFourier_scaled_continuous s hny ((n : ℕ) : ℤ)

theorem completed_integer_dilation_mean (s : ℂ) (n : ℕ+)
    (y : ℝ) (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1,
      completedActualEisenstein s (pnatDilate n (horizontalPoint y hy x))) =
        completedConstant ((n : ℝ) * y) s := by
  have hny : 0 < (n : ℝ) * y := mul_pos (by exact_mod_cast n.pos) hy
  have hnZ : ((n : ℕ) : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr n.ne_zero
  simpa [completedActualEisenstein, pnatDilate, dilate, horizontalPoint,
    Complex.mul_re, Complex.mul_im] using
      completedFourier_integer_mean s hny ((n : ℕ) : ℤ) hnZ

end ImbalancedChen.Part3.CompletedEisensteinIntegerMean20261026a
