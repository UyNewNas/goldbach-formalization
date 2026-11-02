import ImbalancedChen.Part3ActualExceptionalKPacketBudget
import ImbalancedChen.Part3ActualWeightedSpectralBudget
import Mathlib.Tactic

/-!
# Physical exceptional normalization and finite smoothing debit

Source-only J candidate. Physical Y=4*pi*sqrt(A*V*U)/(C*sqrt Z)
and rho=V*D/C are inserted explicitly into the existing packet. The actual
Fourier coefficients are charged by their proved weighted L1 theorem.
The output preserves the unsolved spectral coefficient energy. Neither
an Eq24 estimate nor a large-sieve conclusion is assumed.
-/

namespace ImbalancedChen.Part3.ActualExceptionalPhysicalNormalization20261102

noncomputable section
open Set MeasureTheory
open scoped BigOperators
open P3ActualLiteralPacketIntegralSourceOnly
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (actualCoeff)
open P3ActualWeightedSpectralBudgetSourceOnly
open P3ActualSampledLatticeSourceOnly (weightedL1 testWeight)
open ActualCommonHeightKGramSourceOnly (completedPacketSum)
open ActualRealOrderKPacketAdapterSourceOnly
open ActualExceptionalKGlobalBudget20261102
open ActualExceptionalKPacketBudget20261102
open ActualPoissonNormalizedFSourceOnly (spectralScale)
open ImbalancedChen.P3ZExceptionalParameter (tau)
open ImbalancedChen.P3ZExceptionalThresholdGeometry

variable {ι : Type*}

/-- Actual Poisson/spectral scale insertion. All source rows, signed
coefficients and the ONE completed interval/phase are unchanged. -/
def physicalScalePacket (P : PacketData ι) (A C D : ℝ)
    (hA : 0 < A) (hC : 0 < C) : PacketData ι :=
  { P with
    rho := P.V * D / C
    Y0 := spectralScale A P.V P.U P.Z C
    Y0_pos := actual_spectralScale_pos hA P.V_pos P.U_pos P.Z_pos hC }

theorem physicalScalePacket_completed (P : PacketData ι) (A C D : ℝ)
    (hA : 0 < A) (hC : 0 < C) (k : D4 → ℤ) :
    (physicalScalePacket P A C D hA hC).completed k = P.completed k := rfl

theorem physicalScalePacket_completedPacketSum (P : PacketData ι) (A C D : ℝ)
    (hA : 0 < A) (hC : 0 < C) (k : D4 → ℤ) :
    completedPacketSum (physicalScalePacket P A C D hA hC) k =
      completedPacketSum P k := rfl

/-- No scale-identity premise: the returned expression uses the literal
physical spectral scale, the original divisor length U/nu and full pi. -/
theorem physical_transform_sq_le_AJ_weights (P : PacketData ι)
    (k : D4 → ℤ) {A C D nu lambda : ℝ}
    (hA : 0 < A) (hC : 0 < C) (hnu : 0 < nu)
    (hlambda : (975 : ℝ) / 4096 ≤ lambda) :
    ‖realOrderTestTransform (physicalScalePacket P A C D hA hC) k (tau lambda)‖ ^ 2 ≤
      transformBudget (spectralScale A P.V P.U P.Z C) ^ 2 *
        (1 + P.Z / (P.U / nu)) ^ tau lambda *
        max 1 (ratioBound A nu (P.U / nu) P.V P.Z C ^ theta) *
        threshold P.V P.Z ^ tau lambda := by
  have hU : P.U = nu * (P.U / nu) := by field_simp [hnu.ne']
  exact actual_transform_sq_le_AJ_weights (physicalScalePacket P A C D hA hC)
    k hA hnu (div_pos P.U_pos hnu) hC hU rfl hlambda

/-- The literal opposite-sign transform normalization in Pascadi (3.18),
evaluated at doubled exceptional order alpha. This does not assert a
Kuznetsov identity for an arbitrary PacketData. -/
def oppositeSignTestTransform (P : PacketData ι) (k : D4 → ℤ) (alpha : ℝ) : ℂ :=
  (((4 / Real.pi) * Real.cos (Real.pi * alpha / 2) : ℝ) : ℂ) *
    realOrderTestTransform P k alpha

theorem oppositeSignTestTransform_le_power (P : PacketData ι)
    (k : D4 → ℤ) (alpha : ℝ) (halpha : |alpha| ≤ theta) :
    ‖oppositeSignTestTransform P k alpha‖ ≤
      (4 / Real.pi) * transformBudget P.Y0 * (1 + 1 / P.Y0) ^ |alpha| := by
  have hc : ‖(((4 / Real.pi) * Real.cos (Real.pi * alpha / 2) : ℝ) : ℂ)‖ ≤
      4 / Real.pi := by
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos (div_pos (by norm_num : (0 : ℝ) < 4) Real.pi_pos)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (Real.abs_cos_le_one (Real.pi * alpha / 2)) (by positivity : 0 ≤ 4 / Real.pi)
  unfold oppositeSignTestTransform
  rw [norm_mul]
  calc
    _ ≤ (4 / Real.pi) *
        (transformBudget P.Y0 * (1 + 1 / P.Y0) ^ |alpha|) :=
      mul_le_mul hc (realOrderTestTransform_le_power P k alpha halpha)
        (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- A's fixed-level weight lies in its printed range with an absolute
factor two. The extra z^2/L^3 option is retained but is unnecessary. -/
theorem fixed_level_A_range {L Z z : ℝ} (hL : 0 < L) (hZ : 0 < Z) (hZz : Z ≤ z) :
    1 + Z / L ≤ 2 * max (max 1 (z / L)) (z ^ 2 / L ^ 3) := by
  have hzL : Z / L ≤ z / L := div_le_div_of_nonneg_right hZz hL.le
  have h1 : 1 ≤ max (max 1 (z / L)) (z ^ 2 / L ^ 3) :=
    (le_max_left _ _).trans (le_max_left _ _)
  have hz : z / L ≤ max (max 1 (z / L)) (z ^ 2 / L ^ 3) :=
    (le_max_right _ _).trans (le_max_left _ _)
  linarith

/-- Actual finitely reconstructed K-mode integral, before the automorphic
coefficient energy is estimated. All Fourier modes share the old interval. -/
def finiteSeparatedIntegral (P : PacketData ι) (K : Finset (D4 → ℤ)) (alpha : ℝ) : ℂ :=
  ∑ k ∈ K, actualCoeff P.rho P.sigma k *
    (∫ q : ℝ, realOrderModeFunction P (commonRealOrder alpha) k q)

def finiteCompletedEnergy (P : PacketData ι) (K : Finset (D4 → ℤ)) : ℝ :=
  ∑ k ∈ K, ‖actualCoeff P.rho P.sigma k‖ * ‖completedPacketSum P k‖ ^ 2

theorem finiteCompletedEnergy_nonneg (P : PacketData ι) (K : Finset (D4 → ℤ)) :
    0 ≤ finiteCompletedEnergy P K :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (sq_nonneg _))

/-- A genuine finite smoothing/Cauchy payment. The coefficient energy on
the right is explicit, and no spectral estimate for it is a hypothesis. -/
theorem finiteSeparatedIntegral_sq_le (P : PacketData ι)
    (K : Finset (D4 → ℤ)) (alpha : ℝ) (halpha : |alpha| ≤ theta) :
    ‖finiteSeparatedIntegral P K alpha‖ ^ 2 ≤
      (transformBudget P.Y0 * (1 + 1 / P.Y0) ^ |alpha|) ^ 2 *
        actualW P.rho P.sigma 0 * finiteCompletedEnergy P K := by
  let b : ℝ := transformBudget P.Y0 * (1 + 1 / P.Y0) ^ |alpha|
  have hb : 0 ≤ b := mul_nonneg (transformBudget_nonneg P.Y0_pos)
    (Real.rpow_nonneg (by have h := P.Y0_pos; positivity) _)
  have hsum : (∑ k ∈ K, ‖actualCoeff P.rho P.sigma k‖) ≤ actualW P.rho P.sigma 0 := by
    have hs := (P.actual_norm_summable 0).sum_le_tsum K (fun k _ => norm_nonneg _)
    simpa only [actualW, weightedL1, testWeight, pow_zero, mul_one, actualCoeff] using hs
  have htri : ‖finiteSeparatedIntegral P K alpha‖ ≤
      b * ∑ k ∈ K, ‖actualCoeff P.rho P.sigma k‖ * ‖completedPacketSum P k‖ := by
    calc
      _ ≤ ∑ k ∈ K, ‖actualCoeff P.rho P.sigma k *
          (∫ q : ℝ, realOrderModeFunction P (commonRealOrder alpha) k q)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ k ∈ K, b *
          (‖actualCoeff P.rho P.sigma k‖ * ‖completedPacketSum P k‖) := by
        apply Finset.sum_le_sum
        intro k hk
        rw [norm_mul]
        have h := mul_le_mul_of_nonneg_left
          (common_realOrder_modeIntegral_le_power P k alpha halpha)
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

/-- The smooth cost is selected before every physical packet, residue,
mode set and order. The genuine rho=V*D/C cutoff is checked algebraically. -/
theorem exists_physical_finite_smoothing_constant :
    ∃ B : ℝ, 0 < B ∧ ∀ (P : PacketData ι) (A C D x eta alpha : ℝ)
      (hA : 0 < A) (hC : 0 < C),
      0 < D → 1 ≤ x → 0 ≤ eta → P.V ≤ x ^ eta * C / D →
      |P.sigma| ≤ 1 → |alpha| ≤ theta → ∀ K : Finset (D4 → ℤ),
      ‖finiteSeparatedIntegral (physicalScalePacket P A C D hA hC) K alpha‖ ^ 2 ≤
        B * x ^ ((12 : ℝ) * eta) *
          (transformBudget (spectralScale A P.V P.U P.Z C) *
            (1 + 1 / spectralScale A P.V P.U P.Z C) ^ |alpha|) ^ 2 *
          finiteCompletedEnergy (physicalScalePacket P A C D hA hC) K := by
  obtain ⟨B, hB, hbudget⟩ := actual_uniform_xeta_weighted_budget 0
  refine ⟨B, hB, ?_⟩
  intro P A C D x eta alpha hA hC hD hx heta hcut hsigma halpha K
  have hV := P.V_pos
  have hrho : P.V * D / C ≤ x ^ eta := by
    have hVD : P.V * D ≤ x ^ eta * C := (le_div_iff₀ hD).mp hcut
    exact (div_le_iff₀ hC).mpr hVD
  have hW : actualW (P.V * D / C) P.sigma 0 ≤ B * x ^ ((12 : ℝ) * eta) := by
    simpa using (hbudget x hx eta heta (P.V * D / C)
      (by positivity) hrho P.sigma hsigma).2.1
  have hlocal := finiteSeparatedIntegral_sq_le
    (physicalScalePacket P A C D hA hC) K alpha halpha
  have he := finiteCompletedEnergy_nonneg (physicalScalePacket P A C D hA hC) K
  have hmul := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hW
      (sq_nonneg (transformBudget (spectralScale A P.V P.U P.Z C) *
        (1 + 1 / spectralScale A P.V P.U P.Z C) ^ |alpha|))) he
  exact hlocal.trans (by simpa only [physicalScalePacket, mul_assoc, mul_comm, mul_left_comm] using hmul)

end
end ImbalancedChen.Part3.ActualExceptionalPhysicalNormalization20261102
