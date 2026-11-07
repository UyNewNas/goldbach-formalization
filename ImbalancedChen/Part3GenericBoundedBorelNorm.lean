import ImbalancedChen.Part3GenericBoundedBorelCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
Exact norm and norm-error integrals against the native scalar measure for the
actual bounded measurable calculus. Bounded pointwise convergence yields strong
operator convergence at each actual vector by native dominated convergence.
No norm-identity, spectral-measure, or strong-limit premise is assumed. -/
namespace ImbalancedChen.Part3.GenericBoundedBorelNorm20261025a
noncomputable section
open MeasureTheory Filter
open scoped Topology
open ImbalancedChen.Part3.GenericResolventScalarMeasure20261025a
open ImbalancedChen.Part3.GenericResolventCyclicL2Representation20261025a
open ImbalancedChen.Part3.GenericResolventGlobalSpectralAssembly20261025a
open ImbalancedChen.Part3.GenericGlobalScalarMeasureConsistency20261025a
open ImbalancedChen.Part3.GenericGlobalProjectionScalarConsistency20261025a
open ImbalancedChen.Part3.GenericBoundedBorelCalculus20261025a

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R)

theorem integrable_norm_square {X : Type*} [MeasurableSpace X]
    (φ : BoundedBorelFunction X) (μ : Measure X) [IsFiniteMeasure μ] :
    Integrable (fun t => ‖φ t‖ ^ 2) μ := by
  apply (integrable_const (φ.bound ^ 2)).mono'
    (φ.measurable_toFun.norm.pow 2).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun t => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [φ.norm_le_bound t, norm_nonneg (φ t), φ.bound_nonneg]

theorem fiberMultiplier_norm_square (f : H) (φ : BoundedBorelFunction (ResolventSpectrum R))
    (ξ : ScalarL2 R hSA f) :
    ‖fiberMultiplier R hSA f φ ξ‖ ^ 2 =
      ∫ t, ‖φ t‖ ^ 2 * ‖ξ t‖ ^ 2 ∂scalarMeasure R hSA f := by
  rw [scalarL2_norm_square]
  apply integral_congr_ae
  filter_upwards [fiberMultiplier_coe_ae R hSA f φ ξ] with t ht
  rw [ht, norm_mul, mul_pow]

theorem fiberMultiplier_norm_square_weighted (f : H)
    (φ : BoundedBorelFunction (ResolventSpectrum R)) (ξ : ScalarL2 R hSA f) :
    ‖fiberMultiplier R hSA f φ ξ‖ ^ 2 =
      ∫ t, ‖φ t‖ ^ 2 ∂squaredCoordinateMeasure R hSA f ξ := by
  rw [fiberMultiplier_norm_square]
  unfold squaredCoordinateMeasure
  have hm : AEMeasurable (fun t => ENNReal.ofReal (‖ξ t‖ ^ 2)) (scalarMeasure R hSA f) :=
    ((Lp.aestronglyMeasurable ξ).norm.pow 2).aemeasurable.ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul₀ hm
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => mul_comm _ _

/-- Native scalar-measure isometry identity for every bounded Borel function. -/
theorem borelFunctionalCalculus_norm_square
    (φ : BoundedBorelFunction (ResolventSpectrum R)) (u : H) :
    ‖borelFunctionalCalculus R hSA φ u‖ ^ 2 =
      ∫ t, ‖φ t‖ ^ 2 ∂scalarMeasure R hSA u := by
  have hi := integrable_norm_square φ
    (coordinateSumMeasure R hSA ((spectralUnitary R hSA).symm u))
  rw [borelFunctionalCalculus_apply, (spectralUnitary R hSA).norm_map,
    ← spectralSum_norm_square_tsum,
    scalarMeasure_eq_coordinateSumMeasure R hSA u, coordinateSumMeasure,
    integral_sum_measure hi]
  apply tsum_congr
  intro i
  exact fiberMultiplier_norm_square_weighted R hSA (i : H) φ
    (((spectralUnitary R hSA).symm u) i)

/-- Exact error formula for bounded Borel approximants, with actual μ_u. -/
theorem borelFunctionalCalculus_error_norm_square
    (φ ψ : BoundedBorelFunction (ResolventSpectrum R)) (u : H) :
    ‖borelFunctionalCalculus R hSA φ u - borelFunctionalCalculus R hSA ψ u‖ ^ 2 =
      ∫ t, ‖φ t - ψ t‖ ^ 2 ∂scalarMeasure R hSA u := by
  have h := borelFunctionalCalculus_norm_square R hSA (φ.sub ψ) u
  rw [borelFunctionalCalculus_sub, ContinuousLinearMap.sub_apply] at h
  exact h

/-- Scalar-measure-a.e. equality already gives equality at this vector;
pointwise equality on the full spectrum is not required. -/
theorem borelFunctionalCalculus_apply_eq_of_ae
    (φ ψ : BoundedBorelFunction (ResolventSpectrum R)) (u : H)
    (h : φ =ᵐ[scalarMeasure R hSA u] ψ) :
    borelFunctionalCalculus R hSA φ u = borelFunctionalCalculus R hSA ψ u := by
  have hi : (∫ t, ‖φ t - ψ t‖ ^ 2 ∂scalarMeasure R hSA u) = 0 := by
    calc
      _ = ∫ _t : ResolventSpectrum R, (0 : ℝ) ∂scalarMeasure R hSA u := by
        apply integral_congr_ae
        filter_upwards [h] with t ht
        simp only [ht, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)]
      _ = 0 := integral_zero _ _
  have hsq := (borelFunctionalCalculus_error_norm_square R hSA φ ψ u).trans hi
  have hn : ‖borelFunctionalCalculus R hSA φ u - borelFunctionalCalculus R hSA ψ u‖ = 0 := by
    nlinarith [norm_nonneg (borelFunctionalCalculus R hSA φ u - borelFunctionalCalculus R hSA ψ u)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

/-- Bounded Borel convergence, specialized only at the selected vector.
The domination constant is genuine function data, not an assumed operator limit. -/
theorem borelFunctionalCalculus_tendsto_of_ae
    (φ : ℕ → BoundedBorelFunction (ResolventSpectrum R))
    (ψ : BoundedBorelFunction (ResolventSpectrum R)) (u : H)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ n t, ‖φ n t‖ ≤ C)
    (hlim : ∀ᵐ t ∂scalarMeasure R hSA u, Tendsto (fun n => φ n t) atTop (𝓝 (ψ t))) :
    Tendsto (fun n => borelFunctionalCalculus R hSA (φ n) u) atTop
      (𝓝 (borelFunctionalCalculus R hSA ψ u)) := by
  have hdom : ∀ n, ∀ᵐ t ∂scalarMeasure R hSA u,
      ‖‖φ n t - ψ t‖ ^ 2‖ ≤ (C + ψ.bound) ^ 2 := by
    intro n
    exact Filter.Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hn : ‖φ n t - ψ t‖ ≤ C + ψ.bound :=
        (norm_sub_le _ _).trans (add_le_add (hbound n t) (ψ.norm_le_bound t))
      nlinarith [norm_nonneg (φ n t - ψ t), ψ.bound_nonneg]
  have hlimsq : ∀ᵐ t ∂scalarMeasure R hSA u,
      Tendsto (fun n => ‖φ n t - ψ t‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hlim] with t ht
    simpa only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] using
      (ht.sub tendsto_const_nhds).norm.pow 2
  have hint := tendsto_integral_of_dominated_convergence
    (μ := scalarMeasure R hSA u) (fun _ => (C + ψ.bound) ^ 2)
    (fun n => (((φ n).measurable_toFun.sub ψ.measurable_toFun).norm.pow 2).aestronglyMeasurable)
    (integrable_const _) hdom hlimsq
  have hsq : Tendsto
      (fun n => ‖borelFunctionalCalculus R hSA (φ n) u - borelFunctionalCalculus R hSA ψ u‖ ^ 2)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [← borelFunctionalCalculus_error_norm_square, integral_zero] using hint
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq
  simpa only [Function.comp_apply, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsqrt

end
end ImbalancedChen.Part3.GenericBoundedBorelNorm20261025a