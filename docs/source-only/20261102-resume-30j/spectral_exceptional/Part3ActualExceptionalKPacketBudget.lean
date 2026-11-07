import ImbalancedChen.Part3ActualExceptionalKGlobalBudget
import ImbalancedChen.Part3ActualRealOrderKPacketAdapter
import ImbalancedChen.Part3ZExceptionalThresholdGeometry
import Mathlib.Tactic

/-!
# Actual exceptional K packet: power-scale transform payment

Source-only J candidate. This bounds the existing `realOrderTestTransform`,
not an abstract transform supplied by a caller. The old compact region,
actual spectral test, completed interval/phase, and physical dq/q remain.
The final threshold theorem pays its actual transform weight at the
fixed-level A and averaged-level J scales. It asserts no automorphic
Kuznetsov identification or large-sieve conclusion.
-/

namespace ImbalancedChen.Part3.ActualExceptionalKPacketBudget20261102

noncomputable section
open Set MeasureTheory
open scoped BigOperators
open P3ActualLiteralPacketIntegralSourceOnly
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest spectralMode)
open RealOrderKExceptionalSourceOnly
open ActualRealOrderKPacketAdapterSourceOnly
open ActualCommonHeightKGramSourceOnly (completedPacketSum)
open ActualExceptionalKGlobalBudget20261102
open ImbalancedChen.P3ZExceptionalParameter (tau tau_nonneg tau_le_seven_thirtyseconds)
open ImbalancedChen.P3ZExceptionalThresholdGeometry

variable {ι : Type*}

def transformBudget (Y : ℝ) : ℝ :=
  8160 * (2 : ℝ) ^ theta * (16 : ℝ) ^ theta * logBudget (Y / 16) / (1 + Y)

theorem transformBudget_nonneg {Y : ℝ} (hY : 0 < Y) :
    0 ≤ transformBudget Y := by
  have h := logBudget_pos (Y / 16)
  unfold transformBudget
  positivity

/-- The actual K/q extension has a power/log sup budget on the unchanged
physical region. No exponential-in-1/Y estimate is used here. -/
theorem restrictedRealOrderKernel_norm_le_power (P : PacketData ι)
    (alpha : ℝ) (halpha : |alpha| ≤ theta) :
    ‖restrictedRealOrderKernel P alpha halpha‖ ≤
      kernelBudget (P.Y0 / 16) alpha / (P.Y0 / 16) := by
  have ha : 0 < P.Y0 / 16 := by have h := P.Y0_pos; positivity
  have hbudget := kernelBudget_nonneg ha alpha
  apply (ContinuousMap.norm_le _ (div_nonneg hbudget ha.le)).mpr
  intro q
  rw [restrictedRealOrderKernel_eq]
  have haq : P.Y0 / 16 ≤ (q : ℝ) := q.property.1
  have hq : 0 < (q : ℝ) := ha.trans_le haq
  calc
    ‖(realOrderK alpha (q : ℝ) : ℂ) / ((q : ℝ) : ℂ)‖ =
        |realOrderK alpha (q : ℝ)| / (q : ℝ) := by
      simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq]
    _ ≤ kernelBudget (q : ℝ) alpha / (q : ℝ) :=
      div_le_div_of_nonneg_right (realOrderK_global_budget hq halpha) hq.le
    _ ≤ kernelBudget (P.Y0 / 16) alpha / (q : ℝ) :=
      div_le_div_of_nonneg_right (kernelBudget_antitone ha haq alpha) hq.le
    _ ≤ kernelBudget (P.Y0 / 16) alpha / (P.Y0 / 16) := by gcongr

/-- Exact physical support length times the K/q bound: the Y factor from
dq cancels its reciprocal. The constant is (255/16)*16=255. -/
theorem realOrderTestTransform_le_region_budget (P : PacketData ι)
    (k : D4 → ℤ) (alpha : ℝ) (halpha : |alpha| ≤ theta) :
    ‖realOrderTestTransform P k alpha‖ ≤ 255 * kernelBudget (P.Y0 / 16) alpha := by
  have ha : 0 < P.Y0 / 16 := by have h := P.Y0_pos; positivity
  have he : (∫ q in P.region, spectralTest k P.Y0 q *
      ((realOrderK alpha q : ℂ) / (q : ℂ))) = realOrderTestTransform P k alpha := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro q hq
    simp only [spectralTest, spectralMode, P.chi_scaled_zero_off q hq,
      Complex.ofReal_zero, zero_mul]
  have hpoint (q : ℝ) (hq : q ∈ P.region) :
      ‖spectralTest k P.Y0 q * ((realOrderK alpha q : ℂ) / (q : ℂ))‖ ≤
        kernelBudget (P.Y0 / 16) alpha / (P.Y0 / 16) := by
    have hk := (restrictedRealOrderKernel P alpha halpha).norm_coe_le_norm ⟨q, hq⟩
    rw [restrictedRealOrderKernel_eq] at hk
    have hs : ‖spectralTest k P.Y0 q‖ ≤ 1 :=
      PacketData.spectralMode_norm_le_one k (q / P.Y0)
    rw [norm_mul]
    calc
      _ ≤ 1 * ‖(realOrderK alpha q : ℂ) / (q : ℂ)‖ :=
        mul_le_mul_of_nonneg_right hs (norm_nonneg _)
      _ ≤ kernelBudget (P.Y0 / 16) alpha / (P.Y0 / 16) := by
        rw [one_mul]
        exact hk.trans (restrictedRealOrderKernel_norm_le_power P alpha halpha)
  calc
    ‖realOrderTestTransform P k alpha‖ =
        ‖∫ q in P.region, spectralTest k P.Y0 q *
          ((realOrderK alpha q : ℂ) / (q : ℂ))‖ := by rw [he]
    _ ≤ (kernelBudget (P.Y0 / 16) alpha / (P.Y0 / 16)) *
        (volume : Measure ℝ).real P.region :=
      norm_setIntegral_le_of_norm_le_const isCompact_Icc.measure_lt_top hpoint
    _ = 255 * kernelBudget (P.Y0 / 16) alpha := by
      rw [P.region_measure]
      field_simp [P.Y0_pos.ne']
      <;> ring

theorem region_budget_le_canonical {Y alpha : ℝ}
    (hY : 0 < Y) (halpha : |alpha| ≤ theta) :
    255 * kernelBudget (Y / 16) alpha ≤
      transformBudget Y * (1 + 1 / Y) ^ |alpha| := by
  have hp : (1 + 1 / (Y / 16)) ^ |alpha| ≤
      (16 : ℝ) ^ theta * (1 + 1 / Y) ^ |alpha| := by
    have hbase : 1 + 1 / (Y / 16) ≤ 16 * (1 + 1 / Y) := by
      have he : 1 / (Y / 16) = 16 / Y := by field_simp
      rw [he]
      linarith
    calc
      _ ≤ (16 * (1 + 1 / Y)) ^ |alpha| :=
        Real.rpow_le_rpow (by positivity) hbase (abs_nonneg _)
      _ = (16 : ℝ) ^ |alpha| * (1 + 1 / Y) ^ |alpha| :=
        Real.mul_rpow (by norm_num) (by positivity)
      _ ≤ (16 : ℝ) ^ theta * (1 + 1 / Y) ^ |alpha| :=
        mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_le (by norm_num) halpha)
          (Real.rpow_nonneg (by positivity) _)
  have hlog : 0 ≤ logBudget (Y / 16) := (logBudget_pos _).le
  have hnum : 0 ≤ 255 * (2 * (2 : ℝ) ^ theta * logBudget (Y / 16) *
      ((16 : ℝ) ^ theta * (1 + 1 / Y) ^ |alpha|)) := by positivity
  unfold kernelBudget transformBudget
  calc
    _ = (255 * (2 * (2 : ℝ) ^ theta * logBudget (Y / 16) *
        (1 + 1 / (Y / 16)) ^ |alpha|)) / (1 + Y / 16) := by ring
    _ ≤ (255 * (2 * (2 : ℝ) ^ theta * logBudget (Y / 16) *
        ((16 : ℝ) ^ theta * (1 + 1 / Y) ^ |alpha|))) / (1 + Y / 16) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hp (by positivity)) (by norm_num)
    _ ≤ (16 * (255 * (2 * (2 : ℝ) ^ theta * logBudget (Y / 16) *
        ((16 : ℝ) ^ theta * (1 + 1 / Y) ^ |alpha|)))) / (1 + Y) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith only [mul_nonneg hnum (by norm_num : (0 : ℝ) ≤ 15)]
    _ = _ := by ring

/-- Uniform in the Fourier mode k, all levels, the common phase, and all
physical scales. In particular the parameter can approach zero. -/
theorem realOrderTestTransform_le_power (P : PacketData ι)
    (k : D4 → ℤ) (alpha : ℝ) (halpha : |alpha| ≤ theta) :
    ‖realOrderTestTransform P k alpha‖ ≤
      transformBudget P.Y0 * (1 + 1 / P.Y0) ^ |alpha| :=
  (realOrderTestTransform_le_region_budget P k alpha halpha).trans
    (region_budget_le_canonical P.Y0_pos halpha)

/-- The existing finite packet integral consumes the quantitative
transform bound, preserving every original row and n interference. -/
theorem common_realOrder_modeIntegral_le_power (P : PacketData ι)
    (k : D4 → ℤ) (alpha : ℝ) (halpha : |alpha| ≤ theta) :
    ‖∫ q : ℝ, realOrderModeFunction P (commonRealOrder alpha) k q‖ ≤
      transformBudget P.Y0 * (1 + 1 / P.Y0) ^ |alpha| *
        ‖completedPacketSum P k‖ := by
  rw [actual_common_realOrder_modeIntegral, norm_mul]
  exact mul_le_mul_of_nonneg_right
    (realOrderTestTransform_le_power P k alpha halpha) (norm_nonneg _)

/-- Exact square split into A's fixed-level weight X0 and J's enlarged
weight (1+X/sqrt(X0))^2. No spectral estimate is a premise. -/
theorem square_weight_split {X X0 exponent : ℝ}
    (hX : 0 ≤ X) (hX0 : 1 ≤ X0) (he : 0 ≤ exponent) :
    ((1 + X) ^ exponent) ^ 2 ≤
      X0 ^ exponent * ((1 + X / Real.sqrt X0) ^ 2) ^ exponent := by
  have hX0p : 0 < X0 := lt_of_lt_of_le zero_lt_one hX0
  have hrp : 0 < Real.sqrt X0 := Real.sqrt_pos.mpr hX0p
  have hr2 : Real.sqrt X0 ^ 2 = X0 := Real.sq_sqrt hX0p.le
  have hr1 : 1 ≤ Real.sqrt X0 := by
    nlinarith [Real.sqrt_nonneg X0]
  have heq : X0 * (1 + X / Real.sqrt X0) ^ 2 = (Real.sqrt X0 + X) ^ 2 := by
    have hm : Real.sqrt X0 * (1 + X / Real.sqrt X0) = Real.sqrt X0 + X := by
      field_simp [hrp.ne']
      <;> ring
    calc
      _ = (Real.sqrt X0 * (1 + X / Real.sqrt X0)) ^ 2 := by rw [mul_pow, hr2]
      _ = _ := by rw [hm]
  have hbase : (1 + X) ^ 2 ≤ X0 * (1 + X / Real.sqrt X0) ^ 2 := by
    rw [heq]
    nlinarith [mul_nonneg (sub_nonneg.mpr hr1) hX]
  have hpower : ((1 + X) ^ exponent) ^ 2 = ((1 + X) ^ 2) ^ exponent := by
    calc
      _ = (1 + X) ^ (exponent * (2 : ℝ)) :=
        (Real.rpow_mul_natCast (by positivity : 0 ≤ 1 + X) exponent 2).symm
      _ = (1 + X) ^ ((2 : ℝ) * exponent) := by congr 1; ring
      _ = _ := Real.rpow_natCast_mul (by positivity : 0 ≤ 1 + X) 2 exponent
  rw [hpower, ← Real.mul_rpow hX0p.le (sq_nonneg _)]
  exact Real.rpow_le_rpow (sq_nonneg _) hbase he

/-- The actual physical-scale transform is paid at the literal A/J
thresholds. The lambda lower bound is explicitly conditional; this file
does not manufacture a Kim--Sarnak theorem for arbitrary lambda. -/
theorem actual_transform_sq_le_AJ_weights (P : PacketData ι)
    (k : D4 → ℤ) {A nu L C lambda : ℝ}
    (hA : 0 < A) (hnu : 0 < nu) (hL : 0 < L) (hC : 0 < C)
    (hU : P.U = nu * L)
    (hY : P.Y0 = ActualPoissonNormalizedFSourceOnly.spectralScale A P.V P.U P.Z C)
    (hlambda : (975 : ℝ) / 4096 ≤ lambda) :
    ‖realOrderTestTransform P k (tau lambda)‖ ^ 2 ≤
      transformBudget P.Y0 ^ 2 * (1 + P.Z / L) ^ tau lambda *
        max 1 (ratioBound A nu L P.V P.Z C ^ theta) *
        threshold P.V P.Z ^ tau lambda := by
  have hYpos := P.Y0_pos
  have hZpos := P.Z_pos
  have ht : |tau lambda| ≤ theta := by
    rw [abs_of_nonneg (tau_nonneg lambda)]
    exact tau_le_seven_thirtyseconds hlambda
  have hbound := realOrderTestTransform_le_power P k (tau lambda) ht
  rw [abs_of_nonneg (tau_nonneg lambda)] at hbound
  have hsquare : ‖realOrderTestTransform P k (tau lambda)‖ ^ 2 ≤
      transformBudget P.Y0 ^ 2 * ((1 + 1 / P.Y0) ^ tau lambda) ^ 2 := by
    have hnonneg : 0 ≤ transformBudget P.Y0 * (1 + 1 / P.Y0) ^ tau lambda :=
      mul_nonneg (transformBudget_nonneg P.Y0_pos) (Real.rpow_nonneg (by positivity) _)
    simpa only [mul_pow, pow_two] using
      mul_le_mul hbound hbound (norm_nonneg _) hnonneg
  have hsplit := square_weight_split (X := 1 / P.Y0)
    (X0 := 1 + P.Z / L) (by positivity)
    (by have h := div_nonneg P.Z_pos.le hL.le; linarith) (tau_nonneg lambda)
  have hweight : (1 + 1 / P.Y0 / Real.sqrt (1 + P.Z / L)) ^ 2 =
      spectralWeight A P.V (nu * L) P.Z C L := by
    rw [hY, hU]
    rfl
  rw [hweight] at hsplit
  have hj := spectral_tau_weight_le hA P.V_pos hnu hL P.Z_pos hC hlambda
  calc
    _ ≤ transformBudget P.Y0 ^ 2 * ((1 + 1 / P.Y0) ^ tau lambda) ^ 2 := hsquare
    _ ≤ transformBudget P.Y0 ^ 2 *
        ((1 + P.Z / L) ^ tau lambda * spectralWeight A P.V (nu * L) P.Z C L ^ tau lambda) :=
      mul_le_mul_of_nonneg_left hsplit (sq_nonneg _)
    _ ≤ transformBudget P.Y0 ^ 2 *
        ((1 + P.Z / L) ^ tau lambda *
          (max 1 (ratioBound A nu L P.V P.Z C ^ theta) *
            threshold P.V P.Z ^ tau lambda)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hj (Real.rpow_nonneg (by positivity) _)) (sq_nonneg _)
    _ = _ := by ring

end
end ImbalancedChen.Part3.ActualExceptionalKPacketBudget20261102
