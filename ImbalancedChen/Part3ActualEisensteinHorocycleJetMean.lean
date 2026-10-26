import ImbalancedChen.Part3ActualEisensteinHorocycleRemainder
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-!
# Exact horocycle means of the actual continued nonconstant height jets

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.
The fixed-height actual q-moment series is integrated absolutely.
Mathlib's orthonormal AddCircle characters kill every nonzero frequency,
including every height jet. This proves the genuine y-jet zero mean needed
for mixed Green-current cancellation, without the held Fricke/oldform API.
-/
namespace ImbalancedChen.Part3.ActualEisensteinHorocycleJetMean20261026b
noncomputable section
open Set MeasureTheory
open Part3ActualRamanujanBesselNormalConvergence
open ContinuedFourierSpatialMoments ContinuedFourierMomentSeriesCalculus
open ContinuedFourierNonconstantMaass ActualEisensteinHorocycleRemainder20261026b
local instance periodOne_pos : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

private theorem character_mean_zero (m : ℤ) (hm : m ≠ 0) :
    (∫ x in (0 : ℝ)..1, AddCircle.fourier m (x : AddCircle (1 : ℝ))) = 0 := by
  have h := congrFun (AddCircle.fourierCoeff_fourier (T := (1 : ℝ)) m) 0
  rw [AddCircle.fourierCoeff_eq_intervalIntegral _ 0 0] at h
  simpa only [neg_zero, AddCircle.fourier_zero, one_smul, one_div_one,
    zero_add, Pi.single_apply, if_neg hm.symm, if_neg hm] using h

private theorem phase_eq_signed_character (n : ℕ) (negative : Bool) (x : ℝ) :
    phase (n + 1) (if negative then -x else x) =
      AddCircle.fourier (if negative then -((n + 1 : ℕ) : ℤ) else ((n + 1 : ℕ) : ℤ))
        (x : AddCircle (1 : ℝ)) := by
  cases negative <;> rw [AddCircle.fourier_coe_apply]
  all_goals
    unfold phase
    simp only [Bool.false_eq_true, ↓reduceIte, div_one]
    congr 1
    push_cast
    ring

private theorem momentTerm_signed_mean (k n : ℕ) (s : ℂ) (y : ℝ) (negative : Bool) :
    (∫ x in (0 : ℝ)..1, spatialMomentTerm 0 k n s y (if negative then -x else x)) = 0 := by
  unfold spatialMomentTerm
  simp only [pow_zero, mul_one]
  simp_rw [phase_eq_signed_character]
  rw [intervalIntegral.integral_const_mul, character_mean_zero]
  · simp
  · cases negative <;> simp

private theorem momentTerm_signed_norm (k n : ℕ) (s : ℂ) (y x : ℝ) (negative : Bool) :
    ‖spatialMomentTerm 0 k n s y (if negative then -x else x)‖ =
      ‖spatialMomentTerm 0 k n s y 0‖ := by
  simp only [spatialMomentTerm, norm_mul, norm_phase, mul_one]

private theorem momentTerm_signed_continuous (k n : ℕ) (s : ℂ) (y : ℝ) (negative : Bool) :
    Continuous (fun x : ℝ => spatialMomentTerm 0 k n s y (if negative then -x else x)) := by
  cases negative <;> unfold spatialMomentTerm phase <;> simp only [Bool.false_eq_true,
    ↓reduceIte] <;> fun_prop

private theorem momentSum_signed_continuous (k : ℕ) (s : ℂ) {y : ℝ} (hy : 0 < y) (negative : Bool) :
    Continuous (fun x : ℝ => ∑' n, spatialMomentTerm 0 k n s y (if negative then -x else x)) :=
  continuous_tsum (fun n => momentTerm_signed_continuous k n s y negative)
    (spatialMoment_norm_summable 0 k s hy 0)
    (fun n x => (momentTerm_signed_norm k n s y x negative).le)

private theorem momentSum_signed_mean (k : ℕ) (s : ℂ) {y : ℝ} (hy : 0 < y) (negative : Bool) :
    (∫ x in (0 : ℝ)..1, ∑' n, spatialMomentTerm 0 k n s y (if negative then -x else x)) = 0 := by
  let F : ℕ → ℝ → ℂ := fun n x => spatialMomentTerm 0 k n s y (if negative then -x else x)
  have hi : ∀ n, Integrable (F n) (volume.restrict (Ioc (0 : ℝ) 1)) :=
    fun n => ((momentTerm_signed_continuous k n s y negative).intervalIntegrable 0 1).1
  have hn (n : ℕ) : (∫ x in Ioc (0 : ℝ) 1, ‖F n x‖) = ‖spatialMomentTerm 0 k n s y 0‖ := by
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    simp only [F, momentTerm_signed_norm]
    simp
  have hsum : Summable (fun n => ∫ x in Ioc (0 : ℝ) 1, ‖F n x‖) := by
    simpa only [hn] using spatialMoment_norm_summable 0 k s hy 0
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← integral_tsum_of_summable_integral_norm hi hsum]
  apply tsum_eq_zero
  intro n
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact momentTerm_signed_mean k n s y negative

/-- Every actual signed height q-jet has zero horocycle mean. -/
theorem signedHeightMoment_mean_zero (k : ℕ) (s : ℂ) {y : ℝ} (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1, signedMomentSum 0 k s y x) = 0 := by
  unfold signedMomentSum momentSum
  simp only [pow_zero, one_mul]
  rw [intervalIntegral.integral_add
    ((momentSum_signed_continuous k s hy false).intervalIntegrable 0 1)
    ((momentSum_signed_continuous k s hy true).intervalIntegrable 0 1)]
  simpa only [Bool.false_eq_true, ↓reduceIte, add_zero] using
    congrArg₂ (fun a b : ℂ => a + b)
      (momentSum_signed_mean k s hy false) (momentSum_signed_mean k s hy true)

/-- Actual continued remainder has zero mean, with all completed constants retained. -/
theorem actualRemainder_mean_zero (s : ℂ) {y : ℝ} (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1, actualRemainder s y x) = 0 := by
  simp_rw [actualRemainder_eq_kernel]
  rw [weightedKernel]
  simp_rw [← signedMomentSum_zero_zero_eq_actual s y _ hy]
  rw [intervalIntegral.integral_const_mul, signedHeightMoment_mean_zero 0 s hy, mul_zero]

/-- Exact zero mean of the ACTUAL first-height derivative remainder. -/
theorem actualRemainderY_mean_zero (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    {y : ℝ} (hy : 0 < y) : (∫ x in (0 : ℝ)..1, actualRemainderY s y x) = 0 := by
  simp_rw [actualRemainderY_eq_kernel s hs0 hs1 hy]
  unfold weightedKernelY
  have hc0 : Continuous (fun x => signedMomentSum 0 0 s y x) :=
    continuous_iff_continuousAt.mpr (fun x => (signedMomentSum_hasDerivAt_x 0 0 s y x hy).continuousAt)
  have hc1 : Continuous (fun x => signedMomentSum 0 1 s y x) :=
    continuous_iff_continuousAt.mpr (fun x => (signedMomentSum_hasDerivAt_x 0 1 s y x hy).continuousAt)
  rw [intervalIntegral.integral_add ((hc0.const_mul _).intervalIntegrable 0 1)
    ((hc1.const_mul _).intervalIntegrable 0 1), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, signedHeightMoment_mean_zero 0 s hy,
    signedHeightMoment_mean_zero 1 s hy]
  simp

end
end ImbalancedChen.Part3.ActualEisensteinHorocycleJetMean20261026b

