import ImbalancedChen.Part3PositiveCompactTensorLpApproximation
import ImbalancedChen.Part3MaassGradientUpperSupportClosure
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

An actual exhaustion of the upper chart by compact smooth tensor cutoffs.
The nth cutoff is one on [-n-1,n+1] x [1/(n+2),n+2], is between zero and
one everywhere, and has compact support strictly inside y>0.

For every actual upper-supported planar L2 function, multiplication by
these cutoffs converges in L2. The proof uses the literal cutoff formulas,
an eventual-one argument at each positive point and dominated convergence
with the input's own squared norm. No cutoff convergence or density
hypothesis is assumed. The existing closed supported subspace is consumed
directly at the final endpoint.
-/

namespace ImbalancedChen.Part3.UpperChartSmoothCutoffL2Convergence20261025a

noncomputable section
open MeasureTheory Filter Set
open ImbalancedChen.Part3.PositiveRectangleSmoothTensorDensity20261025a
open ImbalancedChen.Part3.PositiveCompactTensorLpApproximation20261025a
open ImbalancedChen.Part3.CanonicalTensorHyperbolicLaplacianForm20261024z
open ImbalancedChen.Part3.MaassFirstGradientWeakLimit20261025a
open ImbalancedChen.Part3.MaassGradientUpperSupportClosure20261025a

def exhaustionTensor (n : ℕ) : SmoothPositiveTensor :=
  cutoffTensor ((n : ℝ) + 1) (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2)
    (by positivity) (by positivity) (by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < n + 2)).2
      nlinarith [Nat.cast_nonneg (R := ℝ) n])

def exhaustionCutoff (n : ℕ) : (ℝ × ℝ) → ℂ := planeTensor (exhaustionTensor n)

theorem exhaustionCutoff_continuous (n : ℕ) : Continuous (exhaustionCutoff n) :=
  planeTensor_continuous (exhaustionTensor n)

theorem exhaustionCutoff_compact (n : ℕ) : HasCompactSupport (exhaustionCutoff n) :=
  planeTensor_compact (exhaustionTensor n)

theorem exhaustionCutoff_zero_outside (n : ℕ) (p : ℝ × ℝ)
    (hp : p ∉ upperChart) : exhaustionCutoff n p = 0 := by
  have hv : (exhaustionTensor n).vertical p.2 = 0 :=
    image_eq_zero_of_notMem_tsupport
      (fun h => hp ((exhaustionTensor n).vertical_positive h))
  simp [exhaustionCutoff, planeTensor, hv]

theorem exhaustionCutoff_real_range (n : ℕ) (p : ℝ × ℝ) :
    ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 ∧ exhaustionCutoff n p = (r : ℂ) := by
  let r := (exhaustionTensor n).horizontal p.1 * (exhaustionTensor n).vertical p.2
  have hx0 : 0 ≤ (exhaustionTensor n).horizontal p.1 := (horizontalBump _ _).nonneg
  have hx1 : (exhaustionTensor n).horizontal p.1 ≤ 1 := (horizontalBump _ _).le_one
  have hy0 : 0 ≤ (exhaustionTensor n).vertical p.2 := (verticalBump _ _ _ _).nonneg
  have hy1 : (exhaustionTensor n).vertical p.2 ≤ 1 := (verticalBump _ _ _ _).le_one
  refine ⟨r, mul_nonneg hx0 hy0, ?_, rfl⟩
  dsimp only [r]
  nlinarith

theorem exhaustionCutoff_norm_le_one (n : ℕ) (p : ℝ × ℝ) :
    ‖exhaustionCutoff n p‖ ≤ 1 := by
  obtain ⟨r, hr0, hr1, hr⟩ := exhaustionCutoff_real_range n p
  rw [hr, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
  exact hr1

theorem one_sub_exhaustionCutoff_norm_le_one (n : ℕ) (p : ℝ × ℝ) :
    ‖1 - exhaustionCutoff n p‖ ≤ 1 := by
  obtain ⟨r, hr0, hr1, hr⟩ := exhaustionCutoff_real_range n p
  rw [hr, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hr1)]
  linarith

theorem exhaustion_error_norm_le (n : ℕ) (F : (ℝ × ℝ) → ℂ) (p : ℝ × ℝ) :
    ‖F p - exhaustionCutoff n p * F p‖ ≤ ‖F p‖ := by
  have heq : F p - exhaustionCutoff n p * F p =
      (1 - exhaustionCutoff n p) * F p := by ring
  rw [heq, norm_mul]
  exact (mul_le_mul_of_nonneg_right
    (one_sub_exhaustionCutoff_norm_le_one n p) (norm_nonneg _)).trans_eq (one_mul _)

/-- Each fixed positive point eventually lies in the inner one-region;
no unproved claim of uniform convergence on the whole chart is used. -/
theorem eventually_exhaustionCutoff_eq_one (p : ℝ × ℝ) (hp : 0 < p.2) :
    ∀ᶠ n : ℕ in atTop, exhaustionCutoff n p = 1 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max |p.1| (max p.2 (1 / p.2)))
  filter_upwards [eventually_ge_atTop N] with n hn
  have hcast : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hx : |p.1| < (n : ℝ) + 1 := by
    have h := (le_max_left |p.1| (max p.2 (1 / p.2))).trans_lt hN
    linarith
  have hy : p.2 ≤ (n : ℝ) + 2 := by
    have h := (le_max_left p.2 (1 / p.2)).trans
      (le_max_right |p.1| (max p.2 (1 / p.2)))
    linarith
  have hinv : 1 / p.2 < (n : ℝ) + 2 := by
    have h := (le_max_right p.2 (1 / p.2)).trans
      (le_max_right |p.1| (max p.2 (1 / p.2)))
    linarith
  have hlo : 1 / ((n : ℝ) + 2) ≤ p.2 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < n + 2)).2
    have hmul := (div_lt_iff₀ hp).mp hinv
    nlinarith
  have hrect : p ∈ rectangle ((n : ℝ) + 1)
      (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2) :=
    ⟨abs_le.mp hx.le, hlo, hy⟩
  have h := congrFun (congrArg (fun f :
      C(rectangle ((n : ℝ) + 1) (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2), ℂ) =>
      (f : _ → ℂ)) (restrict_cutoffTensor ((n : ℝ) + 1)
        (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2) (by positivity) (by positivity)
        (by
          apply (div_le_iff₀ (by positivity : (0 : ℝ) < n + 2)).2
          nlinarith [Nat.cast_nonneg (R := ℝ) n]))) ⟨p, hrect⟩
  exact h

/-- Genuine dominated L2 cutoff convergence for actual measurable inputs.
The support condition concerns the literal representative, almost everywhere. -/
theorem tendsto_cutoff_eLpNorm (F : (ℝ × ℝ) → ℂ)
    (hF : MemLp F 2 (volume : Measure (ℝ × ℝ)))
    (hpositive : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), p ∉ upperChart → F p = 0) :
    Tendsto (fun n : ℕ => eLpNorm
      (fun p => F p - exhaustionCutoff n p * F p) 2 volume) atTop (nhds 0) := by
  let error (n : ℕ) (p : ℝ × ℝ) := F p - exhaustionCutoff n p * F p
  have hmeas (n : ℕ) : AEMeasurable
      (fun p => ‖error n p‖ₑ ^ (2 : ℝ≥0∞).toReal) volume :=
    (hF.aestronglyMeasurable.sub
      ((exhaustionCutoff_continuous n).aestronglyMeasurable.mul
        hF.aestronglyMeasurable)).enorm.pow_const _
  have hbound (n : ℕ) :
      (fun p => ‖error n p‖ₑ ^ (2 : ℝ≥0∞).toReal) ≤ᵐ[volume]
        (fun p => ‖F p‖ₑ ^ (2 : ℝ≥0∞).toReal) := by
    apply Filter.Eventually.of_forall
    intro p
    apply ENNReal.rpow_le_rpow _ ENNReal.toReal_nonneg
    exact_mod_cast exhaustion_error_norm_le n F p
  have hfinite : (∫⁻ p : ℝ × ℝ, ‖F p‖ₑ ^ (2 : ℝ≥0∞).toReal) ≠ ⊤ :=
    (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
      hF.eLpNorm_lt_top).ne
  have hlim : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)),
      Tendsto (fun n : ℕ => ‖error n p‖ₑ ^ (2 : ℝ≥0∞).toReal) atTop (nhds 0) := by
    filter_upwards [hpositive] with p hp
    have hev : ∀ᶠ n : ℕ in atTop, error n p = 0 := by
      by_cases hy : 0 < p.2
      · filter_upwards [eventually_exhaustionCutoff_eq_one p hy] with n hn
        simp [error, hn]
      · have hz : F p = 0 := hp hy
        exact Filter.Eventually.of_forall (fun n => by simp [error, hz])
    apply tendsto_const_nhds.congr'
    filter_upwards [hev] with n hn
    simp [hn]
  have hint : Tendsto (fun n => ∫⁻ p, ‖error n p‖ₑ ^ (2 : ℝ≥0∞).toReal)
      atTop (nhds 0) := by
    simpa using tendsto_lintegral_of_dominated_convergence'
      (fun p => ‖F p‖ₑ ^ (2 : ℝ≥0∞).toReal) hmeas hbound hfinite hlim
  simp only [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
  convert ENNReal.continuous_rpow_const.continuousAt.tendsto.comp hint using 1
  norm_num

/-- Direct use of the actual previously constructed supported L2 subspace. -/
theorem tendsto_cutoff_eLpNorm_of_upperSupported (F : PlaneL2)
    (hF : F ∈ upperSupportedSubmodule) :
    Tendsto (fun n : ℕ => eLpNorm
      (fun p => F p - exhaustionCutoff n p * F p) 2 volume) atTop (nhds 0) :=
  tendsto_cutoff_eLpNorm F (Lp.memLp F) hF

end
end ImbalancedChen.Part3.UpperChartSmoothCutoffL2Convergence20261025a
