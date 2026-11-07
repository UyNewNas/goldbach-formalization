import ImbalancedChen.Part3ActualExceptionalJLargeTransform
import ImbalancedChen.Part3ActualExceptionalJSmallPacketBudget
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED. Join the K-batch small-positive-J branch with
the M large-positive-J branch, then pay the genuine mode derivative cost.
Weight order FOUR in actualW pays the square of the quadratic mode cost;
the original completed-packet energy is unchanged. The complete physical
integral is reached through the already proved HasSum, not a finite-mode
surrogate or a spectral-norm assumption.
-/

namespace ImbalancedChen.Part3.ActualExceptionalJAllScaleBudget20261102

noncomputable section
open Classical Set MeasureTheory Filter
open scoped BigOperators Topology
open P3ActualLiteralPacketIntegralSourceOnly
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (actualCoeff spectralTest)
open P3ActualWeightedSpectralBudgetSourceOnly
open P3ActualSampledLatticeSourceOnly (weightedL1 testWeight)
open ActualCommonHeightKGramSourceOnly (completedPacketSum)
open ActualExceptionalJSmallKernel20261102 ActualExceptionalJPacketAdapter20261102
open ActualExceptionalJSmallPacketBudget20261102
open ActualExceptionalJLargeTransform20261102
open ActualExceptionalPhysicalNormalization20261102
  (physicalScalePacket finiteCompletedEnergy finiteCompletedEnergy_nonneg)
open ActualPoissonNormalizedFSourceOnly (spectralScale)
open ActualExceptionalKGlobalBudget20261102 (theta)
open ActualExceptionalKPacketBudget20261102 (square_weight_split)
open ImbalancedChen.P3ZExceptionalParameter (tau tau_nonneg tau_le_seven_thirtyseconds)
open ImbalancedChen.P3ZExceptionalThresholdGeometry

variable {ι : Type*}

def allScaleTransformBudget (Y : ℝ) : ℝ :=
  if Y ≤ 1/16 then smallTransformBudget Y else largeTransformConstant / (1+Y)

theorem allScaleTransformBudget_nonneg {Y : ℝ} (hY : 0 < Y) :
    0 ≤ allScaleTransformBudget Y := by
  unfold allScaleTransformBudget
  split_ifs
  · exact smallTransformBudget_nonneg hY
  · exact div_nonneg largeTransformConstant_pos.le (by linarith)

/-- Every positive physical scale, including removable alpha=0. The
small branch retains the current alpha rather than replacing it by theta. -/
theorem positive_transform_all_scale (P : PacketData ι) (k : D4 → ℤ)
    {alpha : ℝ} (ha0 : 0 ≤ alpha) (ha : alpha ≤ exceptionalCap) :
    ‖positiveSignTestTransform P k alpha‖ ≤
      allScaleTransformBudget P.Y0 * (1+1/P.Y0)^alpha * modeSize k^2 := by
  have hY := P.Y0_pos
  have hm := modeSize_ge_one k
  have hm2 : 1 ≤ modeSize k^2 := by nlinarith
  have hp : 1 ≤ (1+1/P.Y0)^alpha := Real.one_le_rpow
    (by have hd : 0 ≤ 1/P.Y0 := by positivity; linarith) ha0
  have hs := smallTransformBudget_nonneg hY
  have hl : 0 ≤ largeTransformConstant / (1+P.Y0) := by
    have h := largeTransformConstant_pos
    positivity
  by_cases hsmall : P.Y0 ≤ 1/16
  · rw [allScaleTransformBudget, if_pos hsmall]
    apply (positiveSignTestTransform_le_power P k alpha ha0 ha hsmall).trans
    exact le_mul_of_one_le_right (mul_nonneg hs (by positivity)) hm2
  · rw [allScaleTransformBudget, if_neg hsmall]
    apply (positive_transform_large P k ha0 ha (lt_of_not_ge hsmall)).trans
    exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hl hp) (sq_nonneg _)

theorem positive_modeIntegral_all_scale (P : PacketData ι) (k : D4 → ℤ)
    {alpha : ℝ} (ha0 : 0 ≤ alpha) (ha : alpha ≤ exceptionalCap) :
    ‖∫ q : ℝ, positiveModeFunction P k alpha q‖ ≤
      (allScaleTransformBudget P.Y0 * (1+1/P.Y0)^alpha) *
        modeSize k^2 * ‖completedPacketSum P k‖ := by
  rw [positive_modeIntegral, norm_mul]
  exact mul_le_mul_of_nonneg_right (positive_transform_all_scale P k ha0 ha) (norm_nonneg _)

/-- Literal 4*pi scale and sqrt(Z) cusp width, with no small-Y gate.
This is weight algebra, conditional on the displayed eigenvalue lower
bound; it is not an instantiated automorphic Kim--Sarnak theorem. -/
theorem physical_positive_transform_all_scale_sq_le_AJ_weights (P : PacketData ι)
    (k : D4 → ℤ) {A C D nu lambda : ℝ}
    (hA : 0 < A) (hC : 0 < C) (hnu : 0 < nu)
    (hlambda : (975 : ℝ)/4096 ≤ lambda) :
    ‖positiveSignTestTransform (physicalScalePacket P A C D hA hC) k (tau lambda)‖^2 ≤
      (allScaleTransformBudget (spectralScale A P.V P.U P.Z C) * modeSize k^2)^2 *
        (1+P.Z/(P.U/nu))^tau lambda *
          max 1 (ratioBound A nu (P.U/nu) P.V P.Z C ^ theta) *
            threshold P.V P.Z ^ tau lambda := by
  let Q := physicalScalePacket P A C D hA hC
  let L : ℝ := P.U/nu
  let b : ℝ := allScaleTransformBudget Q.Y0 * modeSize k^2
  have hL : 0 < L := div_pos P.U_pos hnu
  have hU : Q.U = nu*L := by dsimp [Q, L, physicalScalePacket]; field_simp [hnu.ne']
  have hY : Q.Y0 = spectralScale A Q.V Q.U Q.Z C := rfl
  have hy := Q.Y0_pos
  have hb : 0 ≤ b := mul_nonneg (allScaleTransformBudget_nonneg hy) (sq_nonneg _)
  have hcap : tau lambda ≤ exceptionalCap := tau_le_seven_thirtyseconds hlambda
  have hbound : ‖positiveSignTestTransform Q k (tau lambda)‖ ≤
      b * (1+1/Q.Y0)^tau lambda := by
    simpa only [b, mul_assoc, mul_comm, mul_left_comm] using
      positive_transform_all_scale Q k (tau_nonneg lambda) hcap
  have hsquare : ‖positiveSignTestTransform Q k (tau lambda)‖^2 ≤
      b^2 * ((1+1/Q.Y0)^tau lambda)^2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hbound 2
  have hsplit := square_weight_split (X := 1/Q.Y0) (X0 := 1+Q.Z/L)
    (by positivity) (by have h := div_nonneg Q.Z_pos.le hL.le; linarith)
    (tau_nonneg lambda)
  have hweight : (1+1/Q.Y0/Real.sqrt (1+Q.Z/L))^2 =
      spectralWeight A Q.V (nu*L) Q.Z C L := by
    rw [hY, hU]
    rfl
  rw [hweight] at hsplit
  have hj := spectral_tau_weight_le hA Q.V_pos hnu hL Q.Z_pos hC hlambda
  have hfinal : ‖positiveSignTestTransform Q k (tau lambda)‖^2 ≤
      b^2 * (1+Q.Z/L)^tau lambda *
        max 1 (ratioBound A nu L Q.V Q.Z C ^ theta) *
          threshold Q.V Q.Z ^ tau lambda := by
    calc
      _ ≤ b^2 * ((1+1/Q.Y0)^tau lambda)^2 := hsquare
      _ ≤ b^2 * ((1+Q.Z/L)^tau lambda *
          spectralWeight A Q.V (nu*L) Q.Z C L ^ tau lambda) :=
        mul_le_mul_of_nonneg_left hsplit (sq_nonneg _)
      _ ≤ b^2 * ((1+Q.Z/L)^tau lambda *
          (max 1 (ratioBound A nu L Q.V Q.Z C ^ theta) *
            threshold Q.V Q.Z ^ tau lambda)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hj (Real.rpow_nonneg (by positivity) _)) (sq_nonneg _)
      _ = _ := by ring
  simpa only [Q, L, b, physicalScalePacket] using hfinal

/-- No mode powers are hidden in the coefficient energy. Cauchy puts
all four powers in the already source-derived actualW rho sigma 4. -/
theorem finite_positive_all_scale_sq_le (P : PacketData ι)
    (K : Finset (D4 → ℤ)) {alpha : ℝ} (ha0 : 0 ≤ alpha) (ha : alpha ≤ exceptionalCap) :
    ‖finiteSeparatedPositiveIntegral P K alpha‖^2 ≤
      (allScaleTransformBudget P.Y0 * (1+1/P.Y0)^alpha)^2 *
        actualW P.rho P.sigma 4 * finiteCompletedEnergy P K := by
  let b : ℝ := allScaleTransformBudget P.Y0 * (1+1/P.Y0)^alpha
  have hb : 0 ≤ b := mul_nonneg (allScaleTransformBudget_nonneg P.Y0_pos)
    (Real.rpow_nonneg (by have h := P.Y0_pos; positivity) _)
  have hsum : (∑ k ∈ K, ‖actualCoeff P.rho P.sigma k‖ * modeSize k^4) ≤
      actualW P.rho P.sigma 4 := by
    have hs := (P.actual_weighted_summable 4).sum_le_tsum K
      (fun k _ => mul_nonneg (norm_nonneg _) (by unfold testWeight; positivity))
    simpa only [actualW, weightedL1, testWeight, modeSize, actualCoeff] using hs
  have htri : ‖finiteSeparatedPositiveIntegral P K alpha‖ ≤
      b * ∑ k ∈ K, ‖actualCoeff P.rho P.sigma k‖ * modeSize k^2 * ‖completedPacketSum P k‖ := by
    calc
      _ ≤ ∑ k ∈ K, ‖actualCoeff P.rho P.sigma k *
          (∫ q : ℝ, positiveModeFunction P k alpha q)‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ K, b * (‖actualCoeff P.rho P.sigma k‖ *
          modeSize k^2 * ‖completedPacketSum P k‖) := by
        apply Finset.sum_le_sum
        intro k hk
        rw [norm_mul]
        have h := mul_le_mul_of_nonneg_left
          (positive_modeIntegral_all_scale P k ha0 ha)
          (norm_nonneg (actualCoeff P.rho P.sigma k))
        simpa only [b, mul_assoc, mul_comm, mul_left_comm] using h
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul K
    (r := fun k => ‖actualCoeff P.rho P.sigma k‖ * modeSize k^2 * ‖completedPacketSum P k‖)
    (f := fun k => ‖actualCoeff P.rho P.sigma k‖ * modeSize k^4)
    (g := fun k => ‖actualCoeff P.rho P.sigma k‖ * ‖completedPacketSum P k‖^2)
    (fun _ _ => mul_nonneg (norm_nonneg _) (by positivity))
    (fun _ _ => mul_nonneg (norm_nonneg _) (sq_nonneg _))
    (fun _ _ => by apply le_of_eq; ring)
  have hcs' : (∑ k ∈ K, ‖actualCoeff P.rho P.sigma k‖ *
      modeSize k^2 * ‖completedPacketSum P k‖)^2 ≤
      actualW P.rho P.sigma 4 * finiteCompletedEnergy P K :=
    hcs.trans (mul_le_mul_of_nonneg_right hsum (finiteCompletedEnergy_nonneg P K))
  calc
    _ ≤ (b * ∑ k ∈ K, ‖actualCoeff P.rho P.sigma k‖ *
        modeSize k^2 * ‖completedPacketSum P k‖)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) htri 2
    _ ≤ b^2 * (actualW P.rho P.sigma 4 * finiteCompletedEnergy P K) := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left hcs' (sq_nonneg _)
    _ = _ := by dsimp [b]; ring

def originalCoefficientMass (P : PacketData ι) : ℝ :=
  ∑ j ∈ P.rows, ∑ m ∈ P.mCarrier, ∑ n ∈ P.nCarrier j,
    ‖signedCoefficient P.negativeCusp (P.packet j) n‖

theorem completedPacketSum_norm_le_mass (P : PacketData ι) (k : D4 → ℤ) :
    ‖completedPacketSum P k‖ ≤ originalCoefficientMass P := by
  unfold completedPacketSum originalCoefficientMass
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro m hm
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n hn
  rw [norm_mul, P.completed_weight_norm_mem k m hm,
    norm_signedCoefficient_modePacket, one_mul, norm_signedCoefficient]

def completedEnergy (P : PacketData ι) : ℝ :=
  ∑' k : D4 → ℤ, ‖actualCoeff P.rho P.sigma k‖ * ‖completedPacketSum P k‖^2

theorem completedEnergy_summable (P : PacketData ι) :
    Summable (fun k : D4 → ℤ =>
      ‖actualCoeff P.rho P.sigma k‖ * ‖completedPacketSum P k‖^2) := by
  have hs : Summable (fun k : D4 → ℤ => ‖actualCoeff P.rho P.sigma k‖) := by
    simpa only [actualCoeff, testWeight, pow_zero, mul_one] using P.actual_norm_summable 0
  apply Summable.of_nonneg_of_le
    (fun _ => mul_nonneg (norm_nonneg _) (sq_nonneg _))
    (fun k => mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (completedPacketSum_norm_le_mass P k) 2)
      (norm_nonneg _))
    (hs.mul_right (originalCoefficientMass P^2))

theorem completedEnergy_nonneg (P : PacketData ι) : 0 ≤ completedEnergy P :=
  tsum_nonneg (fun _ => mul_nonneg (norm_nonneg _) (sq_nonneg _))

/-- Full physical source, with the same signed coefficients, rho, rows,
common interval and phase. Finite estimates pass to the actual HasSum. -/
theorem positivePhysical_all_scale_sq_le (P : PacketData ι)
    {alpha : ℝ} (ha0 : 0 ≤ alpha) (ha : alpha ≤ exceptionalCap) :
    ‖∫ q : ℝ, positivePhysical P alpha q‖^2 ≤
      (allScaleTransformBudget P.Y0 * (1+1/P.Y0)^alpha)^2 *
        actualW P.rho P.sigma 4 * completedEnergy P := by
  have ht := positivePhysical_hasSum P alpha ha0 ha
  have hleft : Tendsto (fun K : Finset (D4 → ℤ) =>
      ‖finiteSeparatedPositiveIntegral P K alpha‖^2) atTop
      (𝓝 (‖∫ q : ℝ, positivePhysical P alpha q‖^2)) := by
    have ht' : Tendsto (fun K : Finset (D4 → ℤ) =>
        ∑ k ∈ K, actualCoeff P.rho P.sigma k *
          (positiveSignTestTransform P k alpha * completedPacketSum P k))
        atTop (𝓝 (∫ q : ℝ, positivePhysical P alpha q)) := ht
    have h := ht'.norm.pow 2
    simpa only [finiteSeparatedPositiveIntegral, positive_modeIntegral] using h
  have hright : Tendsto (fun K : Finset (D4 → ℤ) =>
      (allScaleTransformBudget P.Y0 * (1+1/P.Y0)^alpha)^2 *
        actualW P.rho P.sigma 4 * finiteCompletedEnergy P K) atTop
      (𝓝 ((allScaleTransformBudget P.Y0 * (1+1/P.Y0)^alpha)^2 *
        actualW P.rho P.sigma 4 * completedEnergy P)) := by
    have he : Tendsto (fun K : Finset (D4 → ℤ) => finiteCompletedEnergy P K)
        atTop (𝓝 (completedEnergy P)) := (completedEnergy_summable P).hasSum
    exact he.const_mul _
  exact le_of_tendsto_of_tendsto hleft hright
    (Eventually.of_forall (fun K => finite_positive_all_scale_sq_le P K ha0 ha))

/-- The constant precedes all packets, scales, modes and orders. With
rho=V*D/C<=x^eta, the actual weighted L1 price is x^(28*eta), not x^(12*eta).
The retained coefficient energy still needs its separate arithmetic and
automorphic estimate. No such estimate is assumed or manufactured here. -/
theorem exists_physical_positive_all_scale_smoothing_constant :
    ∃ B : ℝ, 0 < B ∧ ∀ (P : PacketData ι) (A C D x eta alpha : ℝ)
      (hA : 0 < A) (hC : 0 < C),
      0 < D → 1 ≤ x → 0 ≤ eta → P.V ≤ x^eta*C/D →
      |P.sigma| ≤ 1 → 0 ≤ alpha → alpha ≤ exceptionalCap →
      ‖∫ q : ℝ, positivePhysical (physicalScalePacket P A C D hA hC) alpha q‖^2 ≤
        B * x^((28 : ℝ)*eta) *
          (allScaleTransformBudget (spectralScale A P.V P.U P.Z C) *
            (1+1/spectralScale A P.V P.U P.Z C)^alpha)^2 *
          completedEnergy (physicalScalePacket P A C D hA hC) := by
  obtain ⟨B, hB, hbudget⟩ := actual_uniform_xeta_weighted_budget 4
  refine ⟨B, hB, ?_⟩
  intro P A C D x eta alpha hA hC hD hx heta hcut hsigma ha0 ha
  have hrho : P.V*D/C ≤ x^eta := by
    exact (div_le_iff₀ hC).mpr ((le_div_iff₀ hD).mp hcut)
  have hW : actualW (P.V*D/C) P.sigma 4 ≤ B*x^((28 : ℝ)*eta) := by
    simpa using (hbudget x hx eta heta (P.V*D/C)
      (by have h := P.V_pos; positivity) hrho P.sigma hsigma).2.1
  have hlocal := positivePhysical_all_scale_sq_le
    (physicalScalePacket P A C D hA hC) ha0 ha
  have he := completedEnergy_nonneg (physicalScalePacket P A C D hA hC)
  have hmul := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hW
      (sq_nonneg (allScaleTransformBudget (spectralScale A P.V P.U P.Z C) *
        (1+1/spectralScale A P.V P.U P.Z C)^alpha))) he
  exact hlocal.trans
    (by simpa only [physicalScalePacket, mul_assoc, mul_comm, mul_left_comm] using hmul)

end
end ImbalancedChen.Part3.ActualExceptionalJAllScaleBudget20261102
