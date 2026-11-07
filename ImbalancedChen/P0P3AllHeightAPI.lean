import ImbalancedChen.P0HeightPublicAPI
import Mathlib.Tactic

/-!
SOURCE_WRITTEN / UNCOMPILED / 20261024z-P0. No acceptance credit.
This is an additional concrete integration chain after source-only peer review.
It combines the actual all-height majorant and actual quadratic-height theorem;
it proves no new spectral hypothesis and does not alter the author height file.
-/

namespace ImbalancedChen.Part3.P0P3AllHeightAPISourceOnly
noncomputable section

open Set MeasureTheory
open P3ActualLiteralPacketIntegralSourceOnly
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest spectralMode)
open ImaginaryOrderKBesselSourceOnly
open ImaginaryOrderKExplicitMajorantSourceOnly
open ImaginaryOrderKHeightDecaySourceOnly
open ActualKPacketAdapterSourceOnly
open ActualCommonHeightKGramSourceOnly
open P0HeightPublicAPISourceOnly

variable {ι : Type*}

/-- Elementary arithmetic regularization; concrete uses below supply both
bounds from the actual K theorems, including the nonzero-height premise. -/
lemma combine_constant_and_quadratic {f A B t : ℝ} (hB : 0 ≤ B)
    (h0 : f ≤ A) (h2 : t ≠ 0 → f ≤ B/t^2) :
    f ≤ (A+B)/(1+t^2) := by
  have hmul : f*t^2 ≤ B := by
    by_cases ht : t = 0
    · simpa only [ht, pow_two, mul_zero] using hB
    · exact (le_div_iff₀ (sq_pos_iff.mpr ht)).mp (h2 ht)
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 1+t^2)).mpr
  nlinarith

/-- A literal K/q estimate valid at every real height, including zero. -/
theorem imaginaryOrderK_div_norm_le_allHeight (t : ℝ) {q : ℝ} (hq : 0 < q) :
    ‖(imaginaryOrderK t q : ℂ)/(q : ℂ)‖ ≤ 12/(q^2*(1+t^2)) := by
  have h := combine_constant_and_quadratic (t := t)
    (A := 2/q^2) (B := 10/q^2) (by positivity)
    (imaginaryOrderK_div_norm_le t hq) (by
      intro ht
      simpa only [div_div] using imaginaryOrderK_div_norm_le_quadratic ht hq)
  calc
    ‖(imaginaryOrderK t q : ℂ)/(q : ℂ)‖ ≤ (2/q^2+10/q^2)/(1+t^2) := h
    _ = 12/(q^2*(1+t^2)) := by
      field_simp [hq.ne', ne_of_gt (by positivity : (0 : ℝ) < 1+t^2)]
      <;> ring

/-- The actual physical restricted kernel now needs no t!=0 guard. -/
theorem restrictedKKernel_norm_le_allHeight (P : PacketData ι) (t : ℝ) :
    ‖restrictedKKernel P t‖ ≤ 3072/(P.Y0^2*(1+t^2)) := by
  have h := combine_constant_and_quadratic (t := t)
    (A := 512/P.Y0^2) (B := 2560/P.Y0^2) (by positivity)
    (restrictedKKernel_norm_le P t) (by
      intro ht
      simpa only [div_div] using restrictedKKernel_norm_le_quadratic P ht)
  calc
    ‖restrictedKKernel P t‖ ≤ (512/P.Y0^2+2560/P.Y0^2)/(1+t^2) := h
    _ = 3072/(P.Y0^2*(1+t^2)) := by
      field_simp [P.Y0_pos.ne', ne_of_gt (by positivity : (0 : ℝ) < 1+t^2)]
      <;> ring

/-- Uniform in the actual Fourier mode and every real spectral height. -/
theorem testKIntegrand_norm_le_allHeight (P : PacketData ι) (k : D4 → ℤ)
    (t q : ℝ) (hq : q ∈ P.region) :
    ‖spectralTest k P.Y0 q * ((imaginaryOrderK t q : ℂ)/(q : ℂ))‖ ≤
      3072/(P.Y0^2*(1+t^2)) := by
  have hqnorm : ‖(imaginaryOrderK t q : ℂ)/(q : ℂ)‖ ≤
      3072/(P.Y0^2*(1+t^2)) := by
    have h := (restrictedKKernel P t).norm_coe_le_norm (⟨q, hq⟩ : P.region)
    rw [restrictedKKernel_eq] at h
    exact h.trans (restrictedKKernel_norm_le_allHeight P t)
  rw [norm_mul]
  calc
    ‖spectralTest k P.Y0 q‖ * ‖(imaginaryOrderK t q : ℂ)/(q : ℂ)‖ ≤
        1 * (3072/(P.Y0^2*(1+t^2))) :=
      mul_le_mul (spectralTest_norm_le_one P k q) hqnorm
        (norm_nonneg _) (by norm_num)
    _ = _ := one_mul _

/-- The actual dq/q transform extends its decay budget across height zero. -/
theorem kTestTransform_norm_le_allHeight (P : PacketData ι) (k : D4 → ℤ) (t : ℝ) :
    ‖kTestTransform P k t‖ ≤ 48960/(P.Y0*(1+t^2)) := by
  have hs : (∫ q in P.region, spectralTest k P.Y0 q *
      ((imaginaryOrderK t q : ℂ)/(q : ℂ))) = kTestTransform P k t := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro q hq
    simp only [spectralTest, spectralMode, P.chi_scaled_zero_off q hq,
      Complex.ofReal_zero, zero_mul]
  calc
    ‖kTestTransform P k t‖ = ‖∫ q in P.region,
        spectralTest k P.Y0 q * ((imaginaryOrderK t q : ℂ)/(q : ℂ))‖ := by rw [hs]
    _ ≤ (3072/(P.Y0^2*(1+t^2))) * (volume : Measure ℝ).real P.region :=
      norm_setIntegral_le_of_norm_le_const isCompact_Icc.measure_lt_top
        (fun q hq => testKIntegrand_norm_le_allHeight P k t q hq)
    _ = 48960/(P.Y0*(1+t^2)) := by
      rw [P.region_measure]
      field_simp [P.Y0_pos.ne', ne_of_gt (by positivity : (0 : ℝ) < 1+t^2)]
      <;> ring

/-- Exact common-height factorization with the frozen packet factor intact. -/
theorem common_height_modeIntegral_norm_le_allHeight (P : PacketData ι)
    (k : D4 → ℤ) (t : ℝ) :
    ‖∫ q : ℝ, kModeFunction P (commonHeight t) k q‖ ≤
      (48960/(P.Y0*(1+t^2))) * ‖completedPacketSum P k‖ := by
  rw [actual_common_height_modeIntegral, norm_mul]
  exact mul_le_mul_of_nonneg_right
    (kTestTransform_norm_le_allHeight P k t) (norm_nonneg _)

/-- The corresponding energy bound, also valid at height zero. -/
theorem common_height_modeIntegral_norm_sq_le_allHeight (P : PacketData ι)
    (k : D4 → ℤ) (t : ℝ) :
    ‖∫ q : ℝ, kModeFunction P (commonHeight t) k q‖^2 ≤
      (48960/(P.Y0*(1+t^2)))^2 * ‖completedPacketSum P k‖^2 := by
  have h := common_height_modeIntegral_norm_le_allHeight P k t
  have hr : 0 ≤ (48960/(P.Y0*(1+t^2))) * ‖completedPacketSum P k‖ := by
    have hY := P.Y0_pos
    positivity
  calc
    ‖∫ q : ℝ, kModeFunction P (commonHeight t) k q‖^2 ≤
        ((48960/(P.Y0*(1+t^2))) * ‖completedPacketSum P k‖)^2 := by
      nlinarith [norm_nonneg (∫ q : ℝ, kModeFunction P (commonHeight t) k q)]
    _ = _ := mul_pow _ _ _

end
end ImbalancedChen.Part3.P0P3AllHeightAPISourceOnly

