import ImbalancedChen.Part3ActualExceptionalJPacketAdapter
import ImbalancedChen.Part3ActualExceptionalPhysicalNormalization
import Mathlib.Tactic

/-!
# Positive-sign exceptional J on the actual small physical scale

Source-only K candidate. The small-scale gate Y0<=1/16 ensures that the
ENTIRE existing physical support [Y0/16,16*Y0] lies in (0,1]. Its norm is
derived from the proved normalized kernel, the actual norm-one spectral
test and the exact support measure. The full 4*pi scale and cusp-width
sqrt(Z) then enter the same original A/J weight algebra as the K branch.

No exceptional spectral norm, Eq24, coefficient-energy bound, or ABL
packet removal/cancellation is a premise. Those ports remain separate.
This file makes no all-scale assertion: Y0>1/16 still needs oscillatory
J-transform control. The small-scale condition is explicit at every use.
-/

namespace ImbalancedChen.Part3.ActualExceptionalJSmallPacketBudget20261102

noncomputable section
open Set MeasureTheory
open scoped BigOperators
open P3ActualLiteralPacketIntegralSourceOnly
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest spectralMode actualCoeff)
open P3ActualWeightedSpectralBudgetSourceOnly
open P3ActualSampledLatticeSourceOnly (weightedL1 testWeight)
open ActualCommonHeightKGramSourceOnly (completedPacketSum)
open ActualExceptionalJSmallKernel20261102
open ActualExceptionalJPacketAdapter20261102
open ActualExceptionalKGlobalBudget20261102 (theta)
open ActualExceptionalKPacketBudget20261102 (square_weight_split)
open ActualExceptionalPhysicalNormalization20261102
  (physicalScalePacket finiteCompletedEnergy finiteCompletedEnergy_nonneg)
open ActualPoissonNormalizedFSourceOnly (spectralScale)
open ImbalancedChen.P3ZExceptionalParameter (tau tau_nonneg tau_le_seven_thirtyseconds)
open ImbalancedChen.P3ZExceptionalThresholdGeometry

variable {ι : Type*}

def smallTransformBudget (Y : ℝ) : ℝ :=
  510 * smallKernelConstant * (16 : ℝ) ^ exceptionalCap *
    (1 + |Real.log (Y / 16)|) / (1 + Y)

theorem smallTransformBudget_nonneg {Y : ℝ} (hY : 0 < Y) :
    0 ≤ smallTransformBudget Y := by
  have hB := smallKernelConstant_pos
  unfold smallTransformBudget
  positivity

private theorem region_log_le {a q : ℝ} (ha : 0 < a)
    (haq : a ≤ q) (hq : q ≤ 1) : |Real.log q| ≤ |Real.log a| := by
  have hq0 : 0 < q := ha.trans_le haq
  rw [abs_of_nonpos (Real.log_nonpos hq0.le hq),
    abs_of_nonpos (Real.log_nonpos ha.le (haq.trans hq))]
  exact neg_le_neg (Real.log_le_log ha haq)

/-- The exact physical support length cancels the reciprocal q measure.
No cutoff width, signed coefficient or mode frequency is changed. -/
theorem positiveSignTestTransform_le_region (P : PacketData ι) (k : D4 → ℤ)
    (alpha : ℝ) (ha0 : 0 ≤ alpha) (ha : alpha ≤ exceptionalCap)
    (hsmall : P.Y0 ≤ 1 / 16) :
    ‖positiveSignTestTransform P k alpha‖ ≤
      255 * smallKernelConstant * (1 + |Real.log (P.Y0 / 16)|) *
        (P.Y0 / 16) ^ (-alpha) := by
  have hlo : 0 < P.Y0 / 16 := by have h := P.Y0_pos; positivity
  let b : ℝ := smallKernelConstant * (1 + |Real.log (P.Y0 / 16)|) *
    (P.Y0 / 16) ^ (-alpha)
  have hb : 0 ≤ b := by have hB := smallKernelConstant_pos; dsimp [b]; positivity
  have he : (∫ q in P.region, spectralTest k P.Y0 q *
      (positiveSignKernel alpha q / (q : ℂ))) = positiveSignTestTransform P k alpha := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro q hq
    simp only [spectralTest, spectralMode, P.chi_scaled_zero_off q hq,
      Complex.ofReal_zero, zero_mul]
  have hpoint (q : ℝ) (hq : q ∈ P.region) :
      ‖spectralTest k P.Y0 q * (positiveSignKernel alpha q / (q : ℂ))‖ ≤
        b / (P.Y0 / 16) := by
    have hq0 : 0 < q := hlo.trans_le hq.1
    have hq1 : q ≤ 1 := by have hhi := hq.2; change q ≤ 16 * P.Y0 at hhi; linarith
    have hs : ‖spectralTest k P.Y0 q‖ ≤ 1 :=
      PacketData.spectralMode_norm_le_one k (q / P.Y0)
    have hk : ‖positiveSignKernel alpha q‖ ≤ b := by
      calc
        _ ≤ smallKernelConstant * (1 + |Real.log q|) * q ^ (-alpha) :=
          positiveSignKernel_small_bound ha0 ha ⟨hq0, hq1⟩
        _ ≤ smallKernelConstant * (1 + |Real.log (P.Y0 / 16)|) *
            (P.Y0 / 16) ^ (-alpha) := by
          have hB := smallKernelConstant_pos
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left
              (add_le_add_left (region_log_le hlo hq.1 hq1) 1) hB.le
          · exact Real.rpow_le_rpow_of_nonpos hlo hq.1 (neg_nonpos.mpr ha0)
          · exact Real.rpow_nonneg hq0.le _
          · positivity
        _ = b := rfl
    rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq0]
    calc
      _ ≤ 1 * (b / q) :=
        mul_le_mul hs (div_le_div_of_nonneg_right hk hq0.le)
          (div_nonneg (norm_nonneg _) hq0.le) (by norm_num)
      _ = b / q := one_mul _
      _ ≤ b / (P.Y0 / 16) := by gcongr; exact hq.1
  calc
    _ = ‖∫ q in P.region, spectralTest k P.Y0 q *
        (positiveSignKernel alpha q / (q : ℂ))‖ := by rw [he]
    _ ≤ (b / (P.Y0 / 16)) * (volume : Measure ℝ).real P.region :=
      norm_setIntegral_le_of_norm_le_const isCompact_Icc.measure_lt_top hpoint
    _ = _ := by
      rw [P.region_measure]
      dsimp [b]
      field_simp [P.Y0_pos.ne']
      <;> ring

/-- Preserve the current alpha power when moving from the lower support
endpoint to the physical scale. Only the fixed factor 16^theta is paid. -/
theorem region_power_le {Y alpha : ℝ} (hY : 0 < Y)
    (ha0 : 0 ≤ alpha) (ha : alpha ≤ exceptionalCap) :
    (Y / 16) ^ (-alpha) ≤
      (16 : ℝ) ^ exceptionalCap * (1 + 1 / Y) ^ alpha := by
  calc
    (Y / 16) ^ (-alpha) = (16 : ℝ) ^ alpha * (1 / Y) ^ alpha := by
      rw [Real.div_rpow hY.le (by norm_num : (0 : ℝ) ≤ 16),
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 16), div_inv_eq_mul,
        Real.rpow_neg_eq_inv_rpow, one_div]
      ring
    _ ≤ (16 : ℝ) ^ exceptionalCap * (1 + 1 / Y) ^ alpha := by
      apply mul_le_mul
      · exact Real.rpow_le_rpow_of_exponent_le (by norm_num) ha
      · exact Real.rpow_le_rpow (by positivity) (by linarith) ha0
      · exact Real.rpow_nonneg (by positivity) _
      · positivity

private theorem scalar_budget_le {Y : ℝ} (hY : 0 < Y) (hsmall : Y ≤ 1 / 16) :
    255 * smallKernelConstant * (1 + |Real.log (Y / 16)|) *
      (16 : ℝ) ^ exceptionalCap ≤ smallTransformBudget Y := by
  have hB := smallKernelConstant_pos
  have hb : 0 ≤ 255 * smallKernelConstant * (1 + |Real.log (Y / 16)|) *
      (16 : ℝ) ^ exceptionalCap := by positivity
  have hden : 1 + Y ≤ 2 := by linarith
  unfold smallTransformBudget
  apply (le_div_iff₀ (by positivity : 0 < 1 + Y)).mpr
  have h := mul_le_mul_of_nonneg_left hden hb
  nlinarith only [h]

/-- Actual positive-sign transform bound, uniform in the Fourier mode and
up to the removable order zero, in the explicitly proved scale range. -/
theorem positiveSignTestTransform_le_power (P : PacketData ι) (k : D4 → ℤ)
    (alpha : ℝ) (ha0 : 0 ≤ alpha) (ha : alpha ≤ exceptionalCap)
    (hsmall : P.Y0 ≤ 1 / 16) :
    ‖positiveSignTestTransform P k alpha‖ ≤
      smallTransformBudget P.Y0 * (1 + 1 / P.Y0) ^ alpha := by
  have hB := smallKernelConstant_pos
  calc
    _ ≤ 255 * smallKernelConstant * (1 + |Real.log (P.Y0 / 16)|) *
        (P.Y0 / 16) ^ (-alpha) :=
      positiveSignTestTransform_le_region P k alpha ha0 ha hsmall
    _ ≤ 255 * smallKernelConstant * (1 + |Real.log (P.Y0 / 16)|) *
        ((16 : ℝ) ^ exceptionalCap * (1 + 1 / P.Y0) ^ alpha) :=
      mul_le_mul_of_nonneg_left (region_power_le P.Y0_pos ha0 ha) (by positivity)
    _ ≤ smallTransformBudget P.Y0 * (1 + 1 / P.Y0) ^ alpha := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (scalar_budget_le P.Y0_pos hsmall)
        (Real.rpow_nonneg (by have h := P.Y0_pos; positivity) _)

/-- The original packet sum remains explicit; no counting or spectral
norm of it is smuggled into the kernel estimate. -/
theorem positive_modeIntegral_le_power (P : PacketData ι) (k : D4 → ℤ)
    (alpha : ℝ) (ha0 : 0 ≤ alpha) (ha : alpha ≤ exceptionalCap)
    (hsmall : P.Y0 ≤ 1 / 16) :
    ‖∫ q : ℝ, positiveModeFunction P k alpha q‖ ≤
      smallTransformBudget P.Y0 * (1 + 1 / P.Y0) ^ alpha * ‖completedPacketSum P k‖ := by
  rw [positive_modeIntegral, norm_mul]
  exact mul_le_mul_of_nonneg_right
    (positiveSignTestTransform_le_power P k alpha ha0 ha hsmall) (norm_nonneg _)

/-- The normalized positive J transform has the SAME squared spectral
weight geometry as the opposite-sign K branch, at literal physical Y0.
The bound on lambda is conditional and is not an automorphic instance. -/
theorem actual_positive_transform_small_sq_le_AJ_weights (P : PacketData ι)
    (k : D4 → ℤ) {A nu L C lambda : ℝ}
    (hA : 0 < A) (hnu : 0 < nu) (hL : 0 < L) (hC : 0 < C)
    (hU : P.U = nu * L) (hY : P.Y0 = spectralScale A P.V P.U P.Z C)
    (hsmall : P.Y0 ≤ 1 / 16) (hlambda : (975 : ℝ) / 4096 ≤ lambda) :
    ‖positiveSignTestTransform P k (tau lambda)‖ ^ 2 ≤
      smallTransformBudget P.Y0 ^ 2 * (1 + P.Z / L) ^ tau lambda *
        max 1 (ratioBound A nu L P.V P.Z C ^ theta) *
        threshold P.V P.Z ^ tau lambda := by
  have hYpos := P.Y0_pos
  have hZpos := P.Z_pos
  have hcap : tau lambda ≤ exceptionalCap := tau_le_seven_thirtyseconds hlambda
  have hbound := positiveSignTestTransform_le_power P k (tau lambda)
    (tau_nonneg lambda) hcap hsmall
  have hsquare : ‖positiveSignTestTransform P k (tau lambda)‖ ^ 2 ≤
      smallTransformBudget P.Y0 ^ 2 * ((1 + 1 / P.Y0) ^ tau lambda) ^ 2 := by
    have hn : 0 ≤ smallTransformBudget P.Y0 * (1 + 1 / P.Y0) ^ tau lambda :=
      mul_nonneg (smallTransformBudget_nonneg P.Y0_pos)
        (Real.rpow_nonneg (by positivity) _)
    simpa only [mul_pow, pow_two] using mul_le_mul hbound hbound (norm_nonneg _) hn
  have hsplit := square_weight_split (X := 1 / P.Y0) (X0 := 1 + P.Z / L)
    (by positivity) (by have h := div_nonneg P.Z_pos.le hL.le; linarith) (tau_nonneg lambda)
  have hweight : (1 + 1 / P.Y0 / Real.sqrt (1 + P.Z / L)) ^ 2 =
      spectralWeight A P.V (nu * L) P.Z C L := by
    rw [hY, hU]
    rfl
  rw [hweight] at hsplit
  have hj := spectral_tau_weight_le hA P.V_pos hnu hL P.Z_pos hC hlambda
  calc
    _ ≤ smallTransformBudget P.Y0 ^ 2 * ((1 + 1 / P.Y0) ^ tau lambda) ^ 2 := hsquare
    _ ≤ smallTransformBudget P.Y0 ^ 2 *
        ((1 + P.Z / L) ^ tau lambda * spectralWeight A P.V (nu * L) P.Z C L ^ tau lambda) :=
      mul_le_mul_of_nonneg_left hsplit (sq_nonneg _)
    _ ≤ smallTransformBudget P.Y0 ^ 2 *
        ((1 + P.Z / L) ^ tau lambda *
          (max 1 (ratioBound A nu L P.V P.Z C ^ theta) *
            threshold P.V P.Z ^ tau lambda)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hj (Real.rpow_nonneg (by positivity) _)) (sq_nonneg _)
    _ = _ := by ring

/-- Insert the actual Poisson scale, including 4*pi and cusp width sqrt Z.
The normalized F parameter is rho=V*D/C, exactly as for the K counterpart. -/
theorem physical_positive_transform_small_sq_le_AJ_weights (P : PacketData ι)
    (k : D4 → ℤ) {A C D nu lambda : ℝ}
    (hA : 0 < A) (hC : 0 < C) (hnu : 0 < nu)
    (hsmall : spectralScale A P.V P.U P.Z C ≤ 1 / 16)
    (hlambda : (975 : ℝ) / 4096 ≤ lambda) :
    ‖positiveSignTestTransform (physicalScalePacket P A C D hA hC) k (tau lambda)‖ ^ 2 ≤
      smallTransformBudget (spectralScale A P.V P.U P.Z C) ^ 2 *
        (1 + P.Z / (P.U / nu)) ^ tau lambda *
        max 1 (ratioBound A nu (P.U / nu) P.V P.Z C ^ theta) *
        threshold P.V P.Z ^ tau lambda := by
  have hU : P.U = nu * (P.U / nu) := by field_simp [hnu.ne']
  exact actual_positive_transform_small_sq_le_AJ_weights
    (physicalScalePacket P A C D hA hC) k hA hnu (div_pos P.U_pos hnu) hC
      hU rfl hsmall hlambda

/-- Exact original-scale meaning of the remaining small-profile gate.
The 4096 is 16^2 from the support gate times 16 from (4*pi)^2. -/
theorem physical_small_scale_iff {A V U Z C : ℝ}
    (hA : 0 < A) (hV : 0 < V) (hU : 0 < U) (hZ : 0 < Z) (hC : 0 < C) :
    spectralScale A V U Z C ≤ 1 / 16 ↔
      4096 * Real.pi ^ 2 * A * V * U ≤ C ^ 2 * Z := by
  have hY := actual_spectralScale_pos hA hV hU hZ hC
  have hden : 0 < C ^ 2 * Z := by positivity
  have he := ActualPoissonNormalizedFSourceOnly.spectralScale_sq hA hV hU hZ hC
  constructor
  · intro hsmall
    have hs : spectralScale A V U Z C ^ 2 ≤ (1 / 16 : ℝ) ^ 2 :=
      pow_le_pow_left₀ hY.le hsmall 2
    rw [he] at hs
    have hm := (div_le_iff₀ hden).mp hs
    nlinarith only [hm]
  · intro hsmall
    have hs : spectralScale A V U Z C ^ 2 ≤ (1 / 16 : ℝ) ^ 2 := by
      rw [he]
      apply (div_le_iff₀ hden).mpr
      nlinarith only [hsmall]
    nlinarith only [hs, hY]

def finiteSeparatedPositiveIntegral (P : PacketData ι)
    (K : Finset (D4 → ℤ)) (alpha : ℝ) : ℂ :=
  ∑ k ∈ K, actualCoeff P.rho P.sigma k *
    (∫ q : ℝ, positiveModeFunction P k alpha q)

/-- The actual Fourier L1 debit and the original retained coefficient
energy are separate. The latter is exactly J's finiteCompletedEnergy. -/
theorem finiteSeparatedPositiveIntegral_sq_le (P : PacketData ι)
    (K : Finset (D4 → ℤ)) (alpha : ℝ) (ha0 : 0 ≤ alpha)
    (ha : alpha ≤ exceptionalCap) (hsmall : P.Y0 ≤ 1 / 16) :
    ‖finiteSeparatedPositiveIntegral P K alpha‖ ^ 2 ≤
      (smallTransformBudget P.Y0 * (1 + 1 / P.Y0) ^ alpha) ^ 2 *
        actualW P.rho P.sigma 0 * finiteCompletedEnergy P K := by
  let b : ℝ := smallTransformBudget P.Y0 * (1 + 1 / P.Y0) ^ alpha
  have hb : 0 ≤ b := mul_nonneg (smallTransformBudget_nonneg P.Y0_pos)
    (Real.rpow_nonneg (by have h := P.Y0_pos; positivity) _)
  have hsum : (∑ k ∈ K, ‖actualCoeff P.rho P.sigma k‖) ≤ actualW P.rho P.sigma 0 := by
    have hs := (P.actual_norm_summable 0).sum_le_tsum K (fun k _ => norm_nonneg _)
    simpa only [actualW, weightedL1, testWeight, pow_zero, mul_one, actualCoeff] using hs
  have htri : ‖finiteSeparatedPositiveIntegral P K alpha‖ ≤
      b * ∑ k ∈ K, ‖actualCoeff P.rho P.sigma k‖ * ‖completedPacketSum P k‖ := by
    calc
      _ ≤ ∑ k ∈ K, ‖actualCoeff P.rho P.sigma k *
          (∫ q : ℝ, positiveModeFunction P k alpha q)‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ K, b * (‖actualCoeff P.rho P.sigma k‖ * ‖completedPacketSum P k‖) := by
        apply Finset.sum_le_sum
        intro k hk
        rw [norm_mul]
        have h := mul_le_mul_of_nonneg_left
          (positive_modeIntegral_le_power P k alpha ha0 ha hsmall)
          (norm_nonneg (actualCoeff P.rho P.sigma k))
        simpa only [b, mul_assoc, mul_comm, mul_left_comm] using h
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul K
    (r := fun k => ‖actualCoeff P.rho P.sigma k‖ * ‖completedPacketSum P k‖)
    (f := fun k => ‖actualCoeff P.rho P.sigma k‖)
    (g := fun k => ‖actualCoeff P.rho P.sigma k‖ * ‖completedPacketSum P k‖ ^ 2)
    (fun _ _ => norm_nonneg _)
    (fun _ _ => mul_nonneg (norm_nonneg _) (sq_nonneg _))
    (fun _ _ => by apply le_of_eq; ring)
  have hcs' : (∑ k ∈ K,
      ‖actualCoeff P.rho P.sigma k‖ * ‖completedPacketSum P k‖) ^ 2 ≤
      actualW P.rho P.sigma 0 * finiteCompletedEnergy P K :=
    hcs.trans (mul_le_mul_of_nonneg_right hsum (finiteCompletedEnergy_nonneg P K))
  calc
    _ ≤ (b * ∑ k ∈ K, ‖actualCoeff P.rho P.sigma k‖ * ‖completedPacketSum P k‖) ^ 2 := by
      have hn : 0 ≤ b * ∑ k ∈ K,
          ‖actualCoeff P.rho P.sigma k‖ * ‖completedPacketSum P k‖ :=
        mul_nonneg hb (Finset.sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)))
      simpa only [pow_two] using mul_le_mul htri htri (norm_nonneg _) hn
    _ ≤ b ^ 2 * (actualW P.rho P.sigma 0 * finiteCompletedEnergy P K) := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left hcs' (sq_nonneg _)
    _ = _ := by dsimp [b]; ring

/-- The smoothing constant is selected before every physical packet,
scale, order and finite Fourier set. The retained phase is not recharged. -/
theorem exists_physical_finite_positive_smoothing_constant :
    ∃ B : ℝ, 0 < B ∧ ∀ (P : PacketData ι) (A C D x eta alpha : ℝ)
      (hA : 0 < A) (hC : 0 < C),
      0 < D → 1 ≤ x → 0 ≤ eta → P.V ≤ x ^ eta * C / D →
      |P.sigma| ≤ 1 → 0 ≤ alpha → alpha ≤ exceptionalCap →
      spectralScale A P.V P.U P.Z C ≤ 1 / 16 → ∀ K : Finset (D4 → ℤ),
      ‖finiteSeparatedPositiveIntegral (physicalScalePacket P A C D hA hC) K alpha‖ ^ 2 ≤
        B * x ^ ((12 : ℝ) * eta) *
          (smallTransformBudget (spectralScale A P.V P.U P.Z C) *
            (1 + 1 / spectralScale A P.V P.U P.Z C) ^ alpha) ^ 2 *
          finiteCompletedEnergy (physicalScalePacket P A C D hA hC) K := by
  obtain ⟨B, hB, hbudget⟩ := actual_uniform_xeta_weighted_budget 0
  refine ⟨B, hB, ?_⟩
  intro P A C D x eta alpha hA hC hD hx heta hcut hsigma ha0 ha hsmall K
  have hV := P.V_pos
  have hrho : P.V * D / C ≤ x ^ eta := by
    have hVD : P.V * D ≤ x ^ eta * C := (le_div_iff₀ hD).mp hcut
    exact (div_le_iff₀ hC).mpr hVD
  have hW : actualW (P.V * D / C) P.sigma 0 ≤ B * x ^ ((12 : ℝ) * eta) := by
    simpa using (hbudget x hx eta heta (P.V * D / C)
      (by positivity) hrho P.sigma hsigma).2.1
  have hlocal := finiteSeparatedPositiveIntegral_sq_le
    (physicalScalePacket P A C D hA hC) K alpha ha0 ha hsmall
  have he := finiteCompletedEnergy_nonneg (physicalScalePacket P A C D hA hC) K
  have hmul := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hW
      (sq_nonneg (smallTransformBudget (spectralScale A P.V P.U P.Z C) *
        (1 + 1 / spectralScale A P.V P.U P.Z C) ^ alpha))) he
  exact hlocal.trans
    (by simpa only [physicalScalePacket, mul_assoc, mul_comm, mul_left_comm] using hmul)

end
end ImbalancedChen.Part3.ActualExceptionalJSmallPacketBudget20261102
