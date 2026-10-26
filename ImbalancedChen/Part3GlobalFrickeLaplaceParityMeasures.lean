import ImbalancedChen.Part3GlobalFrickeBorelProjectionCommutation
import ImbalancedChen.Part3GammaPhysicalSpectralSectorReduction

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED / ZERO FORMAL CREDIT.

The EXISTING actualLaplaceBorelProjection and actualLaplaceMeasure use
the same proved inverse-resolvent coordinate and native scalar measure.
Derived native Borel Fricke commutation therefore supplies actual lambda
projection parity reduction and genuine complex cross-coefficient zero.
For arbitrary independent vectors and complex coefficients, the actual
scalar measure splits with exact squared coefficients. No new spectral
model, assumed invariant sector, or cusp/Eisenstein completeness.
-/

noncomputable section

namespace ImbalancedChen.Part3.GlobalFrickeLaplaceParityMeasures20261026b

open Set MeasureTheory
open ImbalancedChen.Part3.ActualHeckeSecondL220261026b
open ImbalancedChen.Part3.GlobalFrickeBorelProjectionCommutation20261026b
open ImbalancedChen.Part3.GlobalFrickeParityProjections20261026b
open ImbalancedChen.Part3.GlobalFrickeParityNativeCalculus20261026b
open ImbalancedChen.Part3.InvolutiveHilbertProjection20261026b
open ImbalancedChen.Part3.Gamma0ActualSmoothQuotientCore20261025a
open ImbalancedChen.Part3.Gamma0ActualWeakRieszResolvent20261025a
open ImbalancedChen.Part3.Gamma0ActualUnboundedScalarMeasure20261025a
open ImbalancedChen.Part3.GammaMeanCenteredScalarMeasure20261026b
open ImbalancedChen.Part3.GammaPhysicalSpectralSectorReduction20261026b
open ImbalancedChen.Part3.GenericResolventScalarMeasure20261025a
open ImbalancedChen.Part3.GenericResolventUnboundedScalarMeasure20261025a

theorem actualLaplaceMeasure_fricke (N : ℕ) [NeZero N] (hN : 0 < N) (f : QuotientL2 N) :
    actualLaplaceMeasure N (frickeL2 N hN f) = actualLaplaceMeasure N f := by
  exact congrArg (fun μ : Measure (ResolventSpectrum (actualGammaResolvent N)) =>
    μ.map (spectralLambda (actualGammaResolvent N))) (actualResolventScalarMeasure_fricke N hN f)

/-- Every true real-lambda Borel projector commutes with actual Fricke. -/
theorem actualLaplaceBorel_fricke (N : ℕ) [NeZero N] (hN : 0 < N)
    (B : Set ℝ) (hB : MeasurableSet B) (f : QuotientL2 N) :
    frickeL2 N hN (actualLaplaceBorelProjection N B hB f) =
      actualLaplaceBorelProjection N B hB (frickeL2 N hN f) :=
  actualBorel_fricke N hN (spectralLambda (actualGammaResolvent N) ⁻¹' B)
    ((measurable_spectralLambda (actualGammaResolvent N)) hB) f

theorem actualLaplaceBorel_plus (N : ℕ) [NeZero N] (hN : 0 < N)
    (B : Set ℝ) (hB : MeasurableSet B) (f : QuotientL2 N) :
    actualLaplaceBorelProjection N B hB (frickePlus N hN f) =
      frickePlus N hN (actualLaplaceBorelProjection N B hB f) :=
  operator_plus N hN _ (actualLaplaceBorel_fricke N hN B hB) f

theorem actualLaplaceBorel_minus (N : ℕ) [NeZero N] (hN : 0 < N)
    (B : Set ℝ) (hB : MeasurableSet B) (f : QuotientL2 N) :
    actualLaplaceBorelProjection N B hB (frickeMinus N hN f) =
      frickeMinus N hN (actualLaplaceBorelProjection N B hB f) :=
  operator_minus N hN _ (actualLaplaceBorel_fricke N hN B hB) f

/-- Actual COMPLEX mixed spectral terms vanish for independent vectors,
not just the real diagonal mass of one vector. -/
theorem actualLaplace_parity_cross_zero (N : ℕ) [NeZero N] (hN : 0 < N)
    (B : Set ℝ) (hB : MeasurableSet B) (f g : QuotientL2 N) :
    inner ℂ (actualLaplaceBorelProjection N B hB (frickePlus N hN f)) (frickeMinus N hN g) = 0 := by
  rw [actualLaplaceBorel_plus]
  exact fricke_parity_orthogonal N hN _ _

theorem actualLaplace_parity_projected_cross_zero (N : ℕ) [NeZero N] (hN : 0 < N)
    (B C : Set ℝ) (hB : MeasurableSet B) (hC : MeasurableSet C) (f g : QuotientL2 N) :
    inner ℂ (actualLaplaceBorelProjection N B hB (frickePlus N hN f))
      (actualLaplaceBorelProjection N C hC (frickeMinus N hN g)) = 0 := by
  rw [actualLaplaceBorel_plus, actualLaplaceBorel_minus]
  exact fricke_parity_orthogonal N hN _ _

/-- The actual measure of an arbitrary complex linear combination of
the two physical Fricke channels has exact squared-coefficient splitting. -/
theorem actualLaplaceMeasure_parity_linear_combination (N : ℕ) [NeZero N] (hN : 0 < N)
    (f g : QuotientL2 N) (a b : ℂ) :
    actualLaplaceMeasure N (a • frickePlus N hN f + b • frickeMinus N hN g) =
      ENNReal.ofReal (‖a‖ ^ 2) • actualLaplaceMeasure N (frickePlus N hN f) +
        ENNReal.ofReal (‖b‖ ^ 2) • actualLaplaceMeasure N (frickeMinus N hN g) := by
  apply Measure.ext
  intro B hB
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  simp only [smul_eq_mul]
  rw [actualLaplaceMeasure_eq_borel_projection_norm_sq N _ B hB,
    actualLaplaceMeasure_eq_borel_projection_norm_sq N (frickePlus N hN f) B hB,
    actualLaplaceMeasure_eq_borel_projection_norm_sq N (frickeMinus N hN g) B hB,
    map_add, map_smul, map_smul]
  have hc : inner ℂ (a • actualLaplaceBorelProjection N B hB (frickePlus N hN f))
      (b • actualLaplaceBorelProjection N B hB (frickeMinus N hN g)) = 0 := by
    rw [inner_smul_left, inner_smul_right,
      actualLaplace_parity_projected_cross_zero N hN B B hB hB f g, mul_zero, mul_zero]
  rw [norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hc,
    norm_smul, norm_smul, mul_pow, mul_pow,
    ENNReal.ofReal_add (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (mul_nonneg (sq_nonneg _) (sq_nonneg _)),
    ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_mul (sq_nonneg _)]

theorem actualLaplaceMeasure_eq_parity_sum (N : ℕ) [NeZero N] (hN : 0 < N) (f : QuotientL2 N) :
    actualLaplaceMeasure N f = actualLaplaceMeasure N (frickePlus N hN f) +
      actualLaplaceMeasure N (frickeMinus N hN f) := by
  have h := actualLaplaceMeasure_parity_linear_combination N hN f f (1 : ℂ) 1
  have hf : frickePlus N hN f + frickeMinus N hN f = f := plus_add_minus _ f
  simpa only [one_smul, hf, norm_one, one_pow, ENNReal.ofReal_one] using h

/-- ALL mixed lambda-spectral coefficients split into genuine parity
blocks, with the actual fixed Borel projection definition retained. -/
theorem actualLaplaceBorel_coefficient_parity_split (N : ℕ) [NeZero N] (hN : 0 < N)
    (B : Set ℝ) (hB : MeasurableSet B) (f g : QuotientL2 N) :
    inner ℂ f (actualLaplaceBorelProjection N B hB g) =
      inner ℂ (frickePlus N hN f) (actualLaplaceBorelProjection N B hB (frickePlus N hN g)) +
        inner ℂ (frickeMinus N hN f) (actualLaplaceBorelProjection N B hB (frickeMinus N hN g)) :=
  operator_coefficient_split N hN _ (actualLaplaceBorel_fricke N hN B hB) f g

end ImbalancedChen.Part3.GlobalFrickeLaplaceParityMeasures20261026b
