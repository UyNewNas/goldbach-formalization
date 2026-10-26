import ImbalancedChen.Part3CompletedEisensteinCuspTail
import ImbalancedChen.Part3ContinuedFourierMomentSeriesCalculus
import Mathlib.Tactic

/-!
# Height-retaining bounds for the actual continued Fourier spatial moments

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.
Existing jet bounds supply normal convergence at a fixed lower height.
Here the actual K q-moment bound retains exp(-3*pi*y/4), uniformly over
the whole closed parameter strip, all x, and y>=1. The frequency factor
remains the already proved summable spatialMajorant at height 1/4.
-/
namespace ImbalancedChen.Part3.ActualEisensteinHeightMomentDecay20261026b
noncomputable section
open Set MeasureTheory
open Part3ActualRamanujanBesselNormalConvergence
open ContinuedFourierSpatialMoments ContinuedFourierMomentSeriesCalculus
open CompletedEisensteinCuspTail20261025a ComplexOrderKQCalculus

def heightMomentMass (j k M : ℕ) : ℝ := ∑' n : ℕ, spatialMajorant j k M (1 / 4) n

theorem spatialMajorant_nonneg (j k M n : ℕ) : 0 ≤ spatialMajorant j k M (1 / 4) n := by
  unfold spatialMajorant
  exact mul_nonneg (mul_nonneg
    (mul_nonneg (qMomentDecayConstant_nonneg _ _ _) (by positivity)) (by positivity))
    (Real.exp_pos _).le

theorem heightMomentMass_nonneg (j k M : ℕ) : 0 ≤ heightMomentMass j k M :=
  tsum_nonneg (spatialMajorant_nonneg j k M)

/-- Literal q-moment spatial jets keep an exponentially decaying height
factor in addition to their summable frequency majorant. -/
theorem spatialMomentTerm_height_bound (j k M n : ℕ) {s : ℂ}
    (hs : |s.re| ≤ (M : ℝ)) {y : ℝ} (hy : 1 ≤ y) (x : ℝ) :
    ‖spatialMomentTerm j k n s y x‖ ≤
      Real.exp (-(3 * Real.pi / 4) * y) * spatialMajorant j k M (1 / 4) n := by
  let N : ℕ := n + 1
  have hN : 0 < N := by dsimp [N]; omega
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy
  have hw : 0 < frequency N := by unfold frequency; positivity
  have hq0 : 0 < 2 * Real.pi * (1 / 4 : ℝ) := by positivity
  have hNy : 1 ≤ (N : ℝ) * y := one_le_mul hN1 hy
  have hq : 2 * Real.pi * (1 / 4 : ℝ) ≤ frequency N * y := by
    unfold frequency
    nlinarith [mul_le_mul_of_nonneg_left hNy (by positivity : 0 ≤ 2 * Real.pi), Real.pi_pos]
  have hnu : |(s - 1 / 2).re| ≤ (M : ℝ) + 1 := by
    have h := abs_sub_le s.re (1 / 2 : ℝ)
    norm_num at h
    simp only [Complex.sub_re, Complex.div_re, Complex.one_re,
      Complex.one_im, Complex.ofNat_re, Complex.ofNat_im]
    norm_num
    linarith
  have hK := qMoment_uniform_exp_bound k hq0 hq hnu
  have he : Real.exp (-(frequency N * y / 2)) ≤
      Real.exp (-(3 * Real.pi / 4) * y) * Real.exp (-(Real.pi / 4) * (N : ℝ)) := by
    simpa only [frequency] using exponential_height_frequency_split N hN hy
  have hK' := hK.trans (mul_le_mul_of_nonneg_left he (qMomentDecayConstant_nonneg _ _ _))
  have hc := spectralCoefficient_norm_bound M n hs
  calc
    _ = ‖spectralCoefficient n s‖ * frequency N ^ j * frequency N ^ k *
        ‖qMoment k (s - 1 / 2) (frequency N * y)‖ := by
      simp only [spatialMomentTerm, N, norm_mul, norm_pow, Complex.norm_I,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw, one_mul, norm_phase, mul_one]
    _ ≤ (N : ℝ) ^ (3 * M + 2) * frequency N ^ j * frequency N ^ k *
        (qMomentDecayConstant k (2 * Real.pi * (1 / 4)) ((M : ℝ) + 1) *
          (Real.exp (-(3 * Real.pi / 4) * y) * Real.exp (-(Real.pi / 4) * (N : ℝ)))) := by
      gcongr
    _ = _ := by
      dsimp [spatialMajorant, frequency, N]
      rw [show Real.pi * (1 / 4 : ℝ) = Real.pi / 4 by ring]
      simp only [mul_pow, pow_add]
      ring

theorem momentSum_height_bound (j k M : ℕ) {s : ℂ}
    (hs : |s.re| ≤ (M : ℝ)) {y : ℝ} (hy : 1 ≤ y) (x : ℝ) :
    ‖momentSum j k s y x‖ ≤
      Real.exp (-(3 * Real.pi / 4) * y) * heightMomentMass j k M := by
  have hg := (spatialMajorant_summable j k M (by norm_num : (0 : ℝ) < 1 / 4)).const_mul
    (Real.exp (-(3 * Real.pi / 4) * y))
  have h := tsum_of_norm_bounded hg.hasSum
    (fun n => spatialMomentTerm_height_bound j k M n hs hy x)
  simpa only [momentSum, heightMomentMass, tsum_mul_left] using h

theorem signedMomentSum_height_bound (j k M : ℕ) {s : ℂ}
    (hs : |s.re| ≤ (M : ℝ)) {y : ℝ} (hy : 1 ≤ y) (x : ℝ) :
    ‖signedMomentSum j k s y x‖ ≤
      (2 * Real.exp (-(3 * Real.pi / 4) * y)) * heightMomentMass j k M := by
  have hp := momentSum_height_bound j k M hs hy x
  have hn := momentSum_height_bound j k M hs hy (-x)
  unfold signedMomentSum
  calc
    _ ≤ ‖momentSum j k s y x‖ + ‖(-1 : ℂ) ^ j * momentSum j k s y (-x)‖ := norm_add_le _ _
    _ = ‖momentSum j k s y x‖ + ‖momentSum j k s y (-x)‖ := by
      simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    _ ≤ _ := by linarith

end
end ImbalancedChen.Part3.ActualEisensteinHeightMomentDecay20261026b
