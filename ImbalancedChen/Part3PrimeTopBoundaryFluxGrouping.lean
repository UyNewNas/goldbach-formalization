import ImbalancedChen.Part3ActualPrimeHorizontalGreenFlux
import ImbalancedChen.Part3ActualHeckeTranslationProjector
import ImbalancedChen.Part3ActualCommonIntervalCompletionL1
import ImbalancedChen.Part3ActualFiniteCosetGreenDivergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

The ORIGINAL actual prime finite-coset trace TOP integral equals the
physical infinity flux at T plus the normalized Fricke-zero flux at T/p.
The true p affine subinterval partition is reused from the literal Hecke
translation projector, with its exact Jacobian and residue-value reindex.
Actual period-one current invariance then translates the union interval
back to [-1/2,1/2]. The Fricke height T/p is retained throughout. This is
valid for every T>0; high-chart or exponential-decay applications would
separately require T>=p and retain the fixed-p decay scale exp(-pi*T/p).
No other cell boundary, quotient Stokes, cusp exhaustiveness, spectral
measure or completeness is asserted, and held8a4 is not imported.
-/

noncomputable section
open Set Complex MeasureTheory
open scoped UpperHalfPlane MatrixGroups BigOperators
open ImbalancedChen.Part3.ActualPrimeHorizontalGreenFlux20261026b
open ImbalancedChen.Part3.PrimeExplicitCosetGreenTrace20261026b
open ImbalancedChen.Part3.PrimeTopFrickeMatrix20261026b
open ImbalancedChen.Part3.ActualPrimeHeckeRealBranch20261026b
open ImbalancedChen.Part3.ActualHeckeTranslationProjector20261026b
open ImbalancedChen.Part3.ActualMaassFourierODE20261026a
open ImbalancedChen.Part3.ActualCommonIntervalCompletionL1SourceOnly
open ImbalancedChen.Part3.SLRealGreenCurrent20261026b
open ImbalancedChen.Part3.Gamma0FiniteCosetGreenTrace20261026b
open ImbalancedChen.Part3.ActualCompletedGamma0Sides20261026b
open ImbalancedChen.Part3.ActualFiniteCosetGreenDivergence20261026b
open ImbalancedChen.Part3.ContinuedFourierSpatialContDiffTwo
open ImbalancedChen.Part3.ActualEisensteinFourierInterchange20261025a
open ImbalancedChen.Part3.AllLevelContinuedMaass20261026a

namespace ImbalancedChen.Part3.PrimeTopBoundaryFluxGrouping20261026b

/-- Reuse of the proved physical affine partition, shifted to the exact
centered top interval. No periodicity is needed for this identity. -/
theorem centered_translationSum_integral (p : ℕ) (hp : 0 < p)
    (f : ℝ → ℂ) (hf : Continuous f) :
    (∫ x in (-(1 / 2) : ℝ)..(1 / 2), translationSum p f x) =
      (p : ℝ) • ∫ t in (-((1 / 2) / (p : ℝ)))..(1 - (1 / 2) / (p : ℝ)), f t := by
  let g : ℝ → ℂ := fun t => f (t - (1 / 2) / (p : ℝ))
  have hg : Continuous g := hf.comp (by fun_prop)
  have hterm (x : ℝ) : translationSum p f (x - 1 / 2) = translationSum p g x := by
    unfold translationSum
    apply Finset.sum_congr rfl
    intro r hr
    apply congrArg f
    dsimp only [g]
    ring
  have hproject : (∫ x in (0 : ℝ)..1, translationSum p g x) =
      (p : ℝ) • ∫ t in (0 : ℝ)..1, g t := by
    simpa [literalCoefficient, phase, AddCircle.fourier_zero] using
      literalCoefficient_translationSum p hp g hg 0
  calc
    _ = ∫ x in (0 : ℝ)..1, translationSum p f (x - 1 / 2) := by
      convert (intervalIntegral.integral_comp_sub_right (translationSum p f)
        (1 / 2 : ℝ) (a := 0) (b := 1)).symm using 1 <;> norm_num
    _ = ∫ x in (0 : ℝ)..1, translationSum p g x := by simp_rw [hterm]
    _ = (p : ℝ) • ∫ t in (0 : ℝ)..1, g t := hproject
    _ = _ := by
      congr 1
      simpa only [g, zero_sub] using
        intervalIntegral.integral_comp_sub_right f ((1 / 2) / (p : ℝ)) (a := 0) (b := 1)

/-- The exact derivative weight cancels the p-fold physical partition.
Period one is used only to translate its full length-one union interval. -/
theorem centered_periodic_affine_partition (p : ℕ) [NeZero p] (hp : 0 < p)
    (f : ℝ → ℂ) (hf : Continuous f) (hper : Function.Periodic f 1) :
    (∫ x in (-(1 / 2) : ℝ)..(1 / 2),
      (p : ℝ)⁻¹ • ∑ r : ZMod p, f ((x + (r.val : ℝ)) / (p : ℝ))) =
      ∫ x in (-(1 / 2) : ℝ)..(1 / 2), f x := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hperiod :
      (∫ t in (-((1 / 2) / (p : ℝ)))..(1 - (1 / 2) / (p : ℝ)), f t) =
        ∫ t in (-(1 / 2) : ℝ)..(1 / 2), f t := by
    convert hper.intervalIntegral_add_eq (-((1 / 2) / (p : ℝ))) (-(1 / 2)) using 1 <;> ring
  have hreindex (x : ℝ) : (∑ r : ZMod p, f ((x + (r.val : ℝ)) / (p : ℝ))) =
      translationSum p f x :=
    sum_zmod_val_reindex p (fun m => f ((x + (m : ℝ)) / (p : ℝ)))
  simp_rw [hreindex]
  rw [intervalIntegral.integral_smul, centered_translationSum_integral p hp f hf,
    hperiod, smul_smul, inv_mul_cancel₀ hpR, one_smul]

/-- The actual intermediate horizontal point has height T/p. -/
theorem finite_branch_horizontalPoint (p : ℕ) (hp : p.Prime) (r : ZMod p)
    (T : ℝ) (hT : 0 < T) (x : ℝ) :
    branchSL p hp.pos (some r) • horizontalPoint T hT x =
      horizontalPoint (T / (p : ℝ))
        (div_pos hT (by exact_mod_cast hp.pos)) ((x + (r.val : ℝ)) / (p : ℝ)) := by
  apply UpperHalfPlane.ext
  rw [branchSL_some_coe]
  ext <;> simp [horizontalPoint, ← Complex.ofReal_natCast, Complex.div_ofReal_re,
    Complex.div_ofReal_im]

/-- Pointwise top density of the ORIGINAL canonical finite trace. -/
theorem actualTrace_top_density_two_channels (p : ℕ) [NeZero p] (hp : p.Prime)
    (s u : ℂ) (hs : s ∈ completedRegularDomain p) (hu : u ∈ completedRegularDomain p)
    (T : ℝ) (hT : 0 < T) (x : ℝ) :
    actualCompletedGreenTrace p s u (horizontalPoint T hT x) (-1) =
      actualInfinityGreenDensity p s u T hT x +
      (p : ℝ)⁻¹ • ∑ r : ZMod p,
        actualFrickeGreenDensity p hp.pos s u (T / (p : ℝ))
          (div_pos hT (by exact_mod_cast hp.pos)) ((x + (r.val : ℝ)) / (p : ℝ)) := by
  rw [actualCompletedGreenTrace_two_channel_pointwise p hp s u hs hu]
  unfold actualInfinityGreenDensity actualFrickeGreenDensity horizontalGreenDensity
  congr 1
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [finite_branch_horizontalPoint p hp r T hT x]
  have hv : (1 / (p : ℂ)) * (-1) = (p : ℝ)⁻¹ • (-1 : ℂ) := by
    simp [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast, one_div]
  rw [hv, greenOneForm_real_smul]

/-- Integral of the original trace TOP, with the literal unequal heights
and no same-height or measure-normalization hypothesis. -/
theorem actualCompletedGreenTrace_top_integral (p : ℕ) [NeZero p] (hp : p.Prime)
    (s u : ℂ) (hs : s ∈ completedRegularDomain p) (hu : u ∈ completedRegularDomain p)
    (T : ℝ) (hT : 0 < T) :
    (∫ x in (-(1 / 2) : ℝ)..(1 / 2),
      actualCompletedGreenTrace p s u (horizontalPoint T hT x) (-1)) =
      actualInfinityGreenFlux p s u T hT +
        actualFrickeGreenFlux p hp.pos s u (T / (p : ℝ))
          (div_pos hT (by exact_mod_cast hp.pos)) := by
  let hTp : 0 < T / (p : ℝ) := div_pos hT (by exact_mod_cast hp.pos)
  let f : ℝ → ℂ := actualFrickeGreenDensity p hp.pos s u (T / (p : ℝ)) hTp
  have hf : Continuous f := actualFrickeGreenDensity_continuous p hp.pos s u _ hTp
  have hper : Function.Periodic f 1 :=
    actualFrickeGreenDensity_periodic p hp.pos s u hs hu _ hTp
  have hsum : Continuous (fun x : ℝ => ∑ r : ZMod p, f ((x + (r.val : ℝ)) / (p : ℝ))) :=
    continuous_finsetSum _ (fun r hr => hf.comp (by fun_prop))
  have hnorm : Continuous (fun x : ℝ =>
      (p : ℝ)⁻¹ • ∑ r : ZMod p, f ((x + (r.val : ℝ)) / (p : ℝ))) :=
    hsum.const_smul _
  simp_rw [actualTrace_top_density_two_channels p hp s u hs hu T hT]
  rw [intervalIntegral.integral_add
    (actualInfinityGreenDensity_intervalIntegrable p s u T hT _ _)
    (hnorm.intervalIntegrable _ _)]
  rw [centered_periodic_affine_partition p hp.pos f hf hper]
  rfl

/-- The exact Y component used by the genuine curved standard-cell Stokes
supplier is this same original trace evaluated on the TOP tangent -1. -/
theorem actualCosetTraceY_top_eq_actualTrace (N : ℕ) [NeZero N] (s u : ℂ)
    (T : ℝ) (hT : 0 < T) (x : ℝ) :
    actualCosetTraceY N s u (x, T) =
      actualCompletedGreenTrace N s u (horizontalPoint T hT x) (-1) := by
  simpa [actualCosetTraceOneForm, coordinateLinear_apply, horizontalPoint] using
    actualCosetTraceOneForm_eq_actualTrace N s u (horizontalPoint T hT x) (-1)

/-- Direct physical top-boundary supplier for the existing actual global
quotient truncated Green identity. The other three sides remain separate. -/
theorem actualCosetTraceY_top_integral_two_cusps (p : ℕ) [NeZero p] (hp : p.Prime)
    (s u : ℂ) (hs : s ∈ completedRegularDomain p) (hu : u ∈ completedRegularDomain p)
    (T : ℝ) (hT : 0 < T) :
    (∫ x in (-(1 / 2) : ℝ)..(1 / 2), actualCosetTraceY p s u (x, T)) =
      actualInfinityGreenFlux p s u T hT +
        actualFrickeGreenFlux p hp.pos s u (T / (p : ℝ))
          (div_pos hT (by exact_mod_cast hp.pos)) := by
  simp_rw [actualCosetTraceY_top_eq_actualTrace p s u T hT]
  exact actualCompletedGreenTrace_top_integral p hp s u hs hu T hT

end ImbalancedChen.Part3.PrimeTopBoundaryFluxGrouping20261026b
