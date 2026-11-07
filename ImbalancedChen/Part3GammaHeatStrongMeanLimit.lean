import ImbalancedChen.Part3GammaHeatMeanInvariant
import ImbalancedChen.Part3Gamma0ActualHeatScalarCoefficient
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

For each actual physical Gamma0 quotient vector the actual heat tends
strongly, as real time tends to infinity, to its genuine constant spectral
projection. The coefficient is the original mean divided by actualVolume.
The proof uses scalar dominated convergence under the same actual finite
Laplace measure, the proved zero-atom identity, and the actual semigroup.
No uniform gap, decay rate, automorphic completeness, or heat-limit premise
is asserted or assumed.
-/
namespace ImbalancedChen.Part3.GammaHeatStrongMeanLimit20261026b

noncomputable section
open Set MeasureTheory Filter Topology
open Gamma0ActualSmoothQuotientCore20261025a
open Gamma0QuotientCellPushforward20261025a
open Gamma0ActualConstantMode20261025a
open Gamma0ActualHeatGenerator20261025a
open Gamma0ActualUnboundedScalarMeasure20261025a
open Gamma0ActualHeatScalarCoefficient20261025a
open GammaConstantRankOneProjection20261026a
open GammaZeroSpectralProjectionKernel20261026a
open GammaZeroAtomConstantClosure20261026a
open GammaHeatMeanInvariant20261026b

/-- A true mean-zero physical vector has strictly positive lambda almost
everywhere for its own actual scalar measure; no positive lower bound. -/
theorem actualLaplaceMeasure_positive_ae_meanZero (N : ℕ) [NeZero N]
    {f : QuotientL2 N} (hf : f ∈ actualMeanZero N) :
    ∀ᵐ lambda ∂actualLaplaceMeasure N f, 0 < lambda := by
  have hm := (mem_actualMeanZero_iff N f).mp hf
  have hz := (actualLaplaceMeasure_zero_eq_zero_iff_mean_zero N f).mpr hm
  have hn : ∀ᵐ lambda ∂actualLaplaceMeasure N f, lambda ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not, Set.setOf_eq_eq_singleton] using hz
  filter_upwards [actualLaplaceMeasure_nonnegative_ae N f, hn] with lambda hl hn
  exact lt_of_le_of_ne hl (Ne.symm hn)

private theorem exp_neg_mul_tendsto_zero {lambda : ℝ} (hl : 0 < lambda) :
    Tendsto (fun t : ℝ => Real.exp (-t * lambda)) atTop (𝓝 0) := by
  have heq : (fun t : ℝ => -t * lambda) = (fun t : ℝ => (-lambda) * t) := by
    funext t
    ring
  change Tendsto (Real.exp ∘ (fun t : ℝ => -t * lambda)) atTop (𝓝 0)
  rw [heq]
  exact Real.tendsto_exp_atBot.comp
    (tendsto_id.const_mul_atTop_of_neg (show -lambda < 0 by linarith))

/-- Exact scalar DCT: domination is one under the actual finite vector
measure, and pointwise decay uses lambda>0 only almost everywhere. -/
theorem actualHeatCoefficient_meanZero_tendsto_zero (N : ℕ) [NeZero N]
    {f : QuotientL2 N} (hf : f ∈ actualMeanZero N) :
    Tendsto (actualHeatCoefficient N f) atTop (𝓝 0) := by
  have hmeas : ∀ t : ℝ, AEStronglyMeasurable
      (fun lambda : ℝ => Real.exp (-t * lambda)) (actualLaplaceMeasure N f) := by
    intro t
    exact (show Continuous (fun lambda : ℝ => Real.exp (-t * lambda)) by
      fun_prop).aestronglyMeasurable
  have hbound : ∀ᶠ t : ℝ in atTop, ∀ᵐ lambda ∂actualLaplaceMeasure N f,
      ‖Real.exp (-t * lambda)‖ ≤ (1 : ℝ) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    filter_upwards [actualLaplaceMeasure_nonnegative_ae N f] with lambda hl
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) hl)
  have hlim : ∀ᵐ lambda ∂actualLaplaceMeasure N f,
      Tendsto (fun t : ℝ => Real.exp (-t * lambda)) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [actualLaplaceMeasure_positive_ae_meanZero N hf] with lambda hl
    exact exp_neg_mul_tendsto_zero hl
  have hDCT : Tendsto
      (fun t : ℝ => ∫ lambda : ℝ, Real.exp (-t * lambda) ∂actualLaplaceMeasure N f)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [integral_zero] using
      (tendsto_integral_filter_of_dominated_convergence (μ := actualLaplaceMeasure N f)
        (fun _lambda : ℝ => (1 : ℝ)) (Eventually.of_forall hmeas) hbound
        (integrable_const (1 : ℝ)) hlim)
  apply hDCT.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact actualHeat_scalar_integral N ht f

/-- The actual self-adjoint semigroup identifies the heat norm with
the scalar coefficient at twice the same real time. -/
theorem actualGammaHeat_norm_sq_eq_twice_coefficient (N : ℕ) [NeZero N]
    {t : ℝ} (ht : 0 ≤ t) (f : QuotientL2 N) :
    ‖actualGammaHeat N t f‖ ^ 2 = actualHeatCoefficient N f (2 * t) := by
  rw [actualHeatCoefficient, show 2 * t = t + t by ring,
    actualGammaHeat_add N ht ht]
  change ‖actualGammaHeat N t f‖ ^ 2 =
    (inner ℂ f (actualGammaHeat N t (actualGammaHeat N t f))).re
  rw [← (actualGammaHeat_selfAdjoint N t).isSymmetric]
  exact InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) _

/-- Strong decay for every actual mean-zero physical vector. The result
is pointwise in the vector and supplies no operator norm decay rate. -/
theorem actualGammaHeat_meanZero_tendsto_zero (N : ℕ) [NeZero N]
    {f : QuotientL2 N} (hf : f ∈ actualMeanZero N) :
    Tendsto (fun t : ℝ => actualGammaHeat N t f) atTop (𝓝 0) := by
  have hdouble : Tendsto (fun t : ℝ => 2 * t) atTop atTop :=
    tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
  have hc := (actualHeatCoefficient_meanZero_tendsto_zero N hf).comp hdouble
  have hsq : Tendsto (fun t : ℝ => ‖actualGammaHeat N t f‖ ^ 2) atTop (𝓝 0) := by
    apply hc.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact (actualGammaHeat_norm_sq_eq_twice_coefficient N ht f).symm
  have hn := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsq
  apply tendsto_iff_norm_sub_tendsto_zero.2
  simpa only [sub_zero, Real.sqrt_zero, Real.sqrt_sq (norm_nonneg _)] using hn

/-- The true heat has the genuine strong equilibrium projection onto
the actual constant line. No hHeatLimit or hMeanPreservation input. -/
theorem actualGammaHeat_tendsto_constantProjection (N : ℕ) [NeZero N]
    (f : QuotientL2 N) :
    Tendsto (fun t : ℝ => actualGammaHeat N t f) atTop (𝓝 (constantRankOne N f)) := by
  have hc := actualGammaHeat_meanZero_tendsto_zero N
    (actualCenteredVector_mem_meanZero N f)
  have hdiff : Tendsto
      (fun t : ℝ => actualGammaHeat N t f - constantRankOne N f) atTop (𝓝 0) := by
    apply hc.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact actualGammaHeat_centered N ht f
  apply tendsto_iff_norm_sub_tendsto_zero.2
  simpa only [norm_zero] using hdiff.norm

/-- Literal physical mean/covolume normalization of the strong limit. -/
theorem actualGammaHeat_tendsto_mean (N : ℕ) [NeZero N] (f : QuotientL2 N) :
    Tendsto (fun t : ℝ => actualGammaHeat N t f) atTop
      (𝓝 (((∫ q, f q ∂carrierPushforward N) / (actualVolume N : ℂ)) • constantL2 N)) := by
  rw [← constantRankOne_apply_mean N f]
  exact actualGammaHeat_tendsto_constantProjection N f

theorem actualGammaHeat_tendsto_actualZeroProjection (N : ℕ) [NeZero N]
    (f : QuotientL2 N) :
    Tendsto (fun t : ℝ => actualGammaHeat N t f) atTop (𝓝 (actualZeroProjection N f)) := by
  rw [actualZeroProjection_eq_constantRankOne]
  exact actualGammaHeat_tendsto_constantProjection N f

end
end ImbalancedChen.Part3.GammaHeatStrongMeanLimit20261026b
