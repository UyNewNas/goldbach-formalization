import ImbalancedChen.Part3ImaginaryOrderKHeightDecay
import ImbalancedChen.Part3ActualCommonHeightKFactorizationFullGram
import Mathlib.Tactic

/-!
SOURCE_WRITTEN / UNCOMPILED / 20261024z-P0. No acceptance credit.

The first import is the proposed module placement of the independently owned
20261024y-P3-ActualK-HeightDecay-SOURCEONLY draft. This file consumes that
source candidate and does not establish its compilation or its analytic core.

Concrete integration of actual K height decay into the existing common-height
factorization API. All statements retain dq/q, P.region, completedPacketSum,
and the original coefficient mass. The transform estimate is uniform in the
Fourier mode. No Kuznetsov normalization or spectral saving is asserted.
-/

namespace ImbalancedChen.Part3.P0HeightPublicAPISourceOnly
noncomputable section

open Set MeasureTheory
open scoped BigOperators
open P3ActualLiteralPacketIntegralSourceOnly
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest spectralMode chi)
open ImaginaryOrderKBesselSourceOnly
open ImaginaryOrderKHeightDecaySourceOnly
open ActualKPacketAdapterSourceOnly
open ActualCommonHeightKGramSourceOnly
open P3ActualWeightedSpectralBudgetSourceOnly (actualW actualW_nonneg)

variable {ι : Type*}

/-- The actual supported test costs at most one, uniformly in its mode. -/
theorem spectralTest_norm_le_one (P : PacketData ι) (k : D4 → ℤ) (q : ℝ) :
    ‖spectralTest k P.Y0 q‖ ≤ 1 := by
  change ‖spectralMode k (q / P.Y0)‖ ≤ 1
  exact PacketData.spectralMode_norm_le_one k (q / P.Y0)

/-- Transfer the actual positive-axis estimate to the literal dq/q transform. -/
theorem testKIntegrand_norm_le_quadratic (P : PacketData ι) (k : D4 → ℤ)
    {t : ℝ} (ht : t ≠ 0) (q : ℝ) (hq : q ∈ P.region) :
    ‖spectralTest k P.Y0 q * ((imaginaryOrderK t q : ℂ) / (q : ℂ))‖ ≤
      2560 / (P.Y0^2 * t^2) := by
  rw [← spectralTest_mul_extendedKKernel P k t q, norm_mul]
  calc
    ‖spectralTest k P.Y0 q‖ *
        ‖extendedKKernel (P.Y0/32) (by have h := P.Y0_pos; positivity) t q‖ ≤
      1 * (2560 / (P.Y0^2 * t^2)) :=
        mul_le_mul (spectralTest_norm_le_one P k q)
          (extendedKKernel_norm_le_quadratic_on_region P ht q hq)
          (norm_nonneg _) (by norm_num)
    _ = _ := one_mul _

/-- The existing exact transform now has a proved explicit height budget. -/
theorem kTestTransform_norm_le_quadratic (P : PacketData ι) (k : D4 → ℤ)
    {t : ℝ} (ht : t ≠ 0) :
    ‖kTestTransform P k t‖ ≤
      (2560 / (P.Y0^2 * t^2)) * ((255/16 : ℝ) * P.Y0) := by
  have hsupport :
      (∫ q in P.region, spectralTest k P.Y0 q *
        ((imaginaryOrderK t q : ℂ)/(q : ℂ))) = kTestTransform P k t := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro q hq
    simp only [spectralTest, spectralMode, P.chi_scaled_zero_off q hq,
      Complex.ofReal_zero, zero_mul]
  rw [← hsupport]
  have hbound := norm_setIntegral_le_of_norm_le_const
    (μ := (volume : Measure ℝ)) isCompact_Icc.measure_lt_top
    (fun q hq => testKIntegrand_norm_le_quadratic P k ht q hq)
  simpa only [P.region_measure] using hbound

/-- Simplified coefficient, with the same dq/q and physical interval. -/
theorem kTestTransform_norm_le_quadratic_simplified (P : PacketData ι)
    (k : D4 → ℤ) {t : ℝ} (ht : t ≠ 0) :
    ‖kTestTransform P k t‖ ≤ 40800 / (P.Y0 * t^2) := by
  calc
    ‖kTestTransform P k t‖ ≤
        (2560 / (P.Y0^2 * t^2)) * ((255/16 : ℝ) * P.Y0) :=
      kTestTransform_norm_le_quadratic P k ht
    _ = 40800 / (P.Y0 * t^2) := by
      field_simp [P.Y0_pos.ne', ht]
      <;> ring

/-- Integration and common-height factorization use exactly the same K. -/
theorem common_height_modeIntegral_norm_le_quadratic (P : PacketData ι)
    (k : D4 → ℤ) {t : ℝ} (ht : t ≠ 0) :
    ‖∫ q : ℝ, kModeFunction P (commonHeight t) k q‖ ≤
      (40800 / (P.Y0 * t^2)) * ‖completedPacketSum P k‖ := by
  rw [actual_common_height_modeIntegral, norm_mul]
  exact mul_le_mul_of_nonneg_right
    (kTestTransform_norm_le_quadratic_simplified P k ht) (norm_nonneg _)

/-- The energy interface retains its literal frozen coefficient energy. -/
theorem common_height_modeIntegral_norm_sq_le_quadratic (P : PacketData ι)
    (k : D4 → ℤ) {t : ℝ} (ht : t ≠ 0) :
    ‖∫ q : ℝ, kModeFunction P (commonHeight t) k q‖^2 ≤
      (40800 / (P.Y0 * t^2))^2 * ‖completedPacketSum P k‖^2 := by
  have h := common_height_modeIntegral_norm_le_quadratic P k ht
  have hr : 0 ≤ (40800 / (P.Y0 * t^2)) * ‖completedPacketSum P k‖ := by
    have hY := P.Y0_pos
    positivity
  calc
    ‖∫ q : ℝ, kModeFunction P (commonHeight t) k q‖^2 ≤
        ((40800 / (P.Y0 * t^2)) * ‖completedPacketSum P k‖)^2 := by
      nlinarith [norm_nonneg (∫ q : ℝ, kModeFunction P (commonHeight t) k q)]
    _ = (40800 / (P.Y0 * t^2))^2 * ‖completedPacketSum P k‖^2 :=
      mul_pow _ _ _

/-- Consumers with a positive shell threshold need no separate nonzero proof. -/
theorem kTestTransform_norm_le_on_shell (P : PacketData ι) (k : D4 → ℤ)
    {T t : ℝ} (hT : 0 < T) (ht : T ≤ |t|) :
    ‖kTestTransform P k t‖ ≤ 40800 / (P.Y0 * T^2) := by
  have htn : t ≠ 0 := by
    intro hzero
    simp only [hzero, abs_zero] at ht
    exact (not_le_of_gt hT) ht
  have hsq : T^2 ≤ t^2 := by
    nlinarith [sq_abs t, abs_nonneg t]
  exact (kTestTransform_norm_le_quadratic_simplified P k htn).trans
    (div_le_div_of_nonneg_left (by norm_num) (by have h := P.Y0_pos; positivity)
      (mul_le_mul_of_nonneg_left hsq P.Y0_pos.le))

/-- Actual PacketData sup norms use the already proved actual K theorem. -/
theorem withKKernel_common_restrictedKernel_norm_le (P : PacketData ι)
    {t : ℝ} (ht : t ≠ 0) (j : ι) (m n : ℕ) :
    ‖(withKKernel P (commonHeight t)).restrictedKernel j m n‖ ≤
      2560 / (P.Y0^2 * t^2) := by
  rw [withKKernel_restrictedKernel]
  exact restrictedKKernel_norm_le_quadratic P ht

/-- The full finite coefficient mass, including every m-copy, is retained. -/
theorem withKKernel_common_mass_le_quadratic (P : PacketData ι)
    {t : ℝ} (ht : t ≠ 0) :
    (withKKernel P (commonHeight t)).mass ≤
      coefficientMass P * (2560 / (P.Y0^2 * t^2)) := by
  calc
    (withKKernel P (commonHeight t)).mass =
        ∑ j ∈ P.rows, ∑ m ∈ P.mCarrier, ∑ n ∈ P.nCarrier j,
          ‖(P.packet j).transformedCoefficient n‖ *
            ‖(withKKernel P (commonHeight t)).restrictedKernel j m n‖ := rfl
    _ ≤ ∑ j ∈ P.rows, ∑ m ∈ P.mCarrier, ∑ n ∈ P.nCarrier j,
          ‖(P.packet j).transformedCoefficient n‖ *
            (2560 / (P.Y0^2 * t^2)) := by
      apply Finset.sum_le_sum
      intro j _hj
      apply Finset.sum_le_sum
      intro m _hm
      apply Finset.sum_le_sum
      intro n _hn
      exact mul_le_mul_of_nonneg_left
        (withKKernel_common_restrictedKernel_norm_le P ht j m n) (norm_nonneg _)
    _ = coefficientMass P * (2560 / (P.Y0^2 * t^2)) := by
      simp only [coefficientMass, Finset.sum_mul]

/-- Propagate the height gain through the original infinite Fourier exchange. -/
theorem k_common_norm_fullIntegral_le_quadratic (P : PacketData ι)
    {t : ℝ} (ht : t ≠ 0) (J0 : ℕ) :
    ‖∫ q : ℝ, kPhysical P (commonHeight t) q‖ ≤
      actualW P.rho P.sigma J0 * coefficientMass P *
        (2560 / (P.Y0^2 * t^2)) * ((255/16 : ℝ) * P.Y0) := by
  have h := (withKKernel P (commonHeight t)).norm_fullIntegral_le J0
  change ‖∫ q : ℝ, (withKKernel P (commonHeight t)).physical q‖ ≤
    actualW P.rho P.sigma J0 * (withKKernel P (commonHeight t)).mass *
      (volume : Measure ℝ).real P.region at h
  rw [withKKernel_physical] at h
  calc
    ‖∫ q : ℝ, kPhysical P (commonHeight t) q‖ ≤
        actualW P.rho P.sigma J0 * (withKKernel P (commonHeight t)).mass *
          (volume : Measure ℝ).real P.region := h
    _ ≤ actualW P.rho P.sigma J0 *
        (coefficientMass P * (2560 / (P.Y0^2 * t^2))) *
          (volume : Measure ℝ).real P.region :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (withKKernel_common_mass_le_quadratic P ht)
          (actualW_nonneg _ _ _)) ENNReal.toReal_nonneg
    _ = actualW P.rho P.sigma J0 * coefficientMass P *
        (2560 / (P.Y0^2 * t^2)) * ((255/16 : ℝ) * P.Y0) := by
      rw [P.region_measure]
      ring

end
end ImbalancedChen.Part3.P0HeightPublicAPISourceOnly

