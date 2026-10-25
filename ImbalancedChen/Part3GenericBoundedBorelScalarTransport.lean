import ImbalancedChen.Part3GenericBoundedBorelNorm

/-! SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
Every bounded Borel coefficient has the actual scalar-measure integral formula.
Pointwise real positivity/order passes to the actual operator. Applying a bounded
Borel function weights the actual scalar measure by its literal norm squared.
-/
namespace ImbalancedChen.Part3.GenericBoundedBorelScalarTransport20261025a
noncomputable section
open MeasureTheory
open ImbalancedChen.Part3.GenericResolventScalarMeasure20261025a
open ImbalancedChen.Part3.GenericResolventCyclicL2Representation20261025a
open ImbalancedChen.Part3.GenericResolventGlobalSpectralAssembly20261025a
open ImbalancedChen.Part3.GenericGlobalScalarMeasureConsistency20261025a
open ImbalancedChen.Part3.GenericGlobalProjectionScalarConsistency20261025a
open ImbalancedChen.Part3.GenericGlobalBorelProjection20261025a
open ImbalancedChen.Part3.GenericBoundedBorelCalculus20261025a
open ImbalancedChen.Part3.GenericBoundedBorelNorm20261025a

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R)

theorem integrable_boundedBorel {X : Type*} [MeasurableSpace X]
    (φ : BoundedBorelFunction X) (μ : Measure X) [IsFiniteMeasure μ] : Integrable φ μ := by
  apply (integrable_const φ.bound).mono' φ.measurable_toFun.aestronglyMeasurable
  exact Filter.Eventually.of_forall φ.norm_le_bound

private theorem star_mul_self (z : ℂ) : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  calc
    star z * z = (Complex.normSq z : ℂ) := by
      simpa only [Complex.star_def] using (Complex.normSq_eq_conj_mul_self (z := z)).symm
    _ = _ := by rw [Complex.normSq_eq_norm_sq]

theorem fiberMultiplier_inner_self (f : H) (φ : BoundedBorelFunction (ResolventSpectrum R))
    (ξ : ScalarL2 R hSA f) :
    inner ℂ ξ (fiberMultiplier R hSA f φ ξ) =
      ∫ t, φ t * ((‖ξ t‖ ^ 2 : ℝ) : ℂ) ∂scalarMeasure R hSA f := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [fiberMultiplier_coe_ae R hSA f φ ξ] with t ht
  rw [ht, RCLike.inner_apply']
  calc
    _ = φ t * (star (ξ t) * ξ t) := by ring
    _ = _ := by rw [star_mul_self]

theorem squaredCoordinateMeasure_integral_borel (f : H) (ξ : ScalarL2 R hSA f)
    (φ : BoundedBorelFunction (ResolventSpectrum R)) :
    (∫ t, φ t ∂squaredCoordinateMeasure R hSA f ξ) =
      ∫ t, φ t * ((‖ξ t‖ ^ 2 : ℝ) : ℂ) ∂scalarMeasure R hSA f := by
  unfold squaredCoordinateMeasure
  have hm : AEMeasurable (fun t => ENNReal.ofReal (‖ξ t‖ ^ 2)) (scalarMeasure R hSA f) :=
    ((Lp.aestronglyMeasurable ξ).norm.pow 2).aemeasurable.ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul₀ hm
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (sq_nonneg _), Complex.real_smul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => mul_comm _ _

theorem borelFunctionalCalculus_integral
    (φ : BoundedBorelFunction (ResolventSpectrum R)) (u : H) :
    (∫ t, φ t ∂scalarMeasure R hSA u) = inner ℂ u (borelFunctionalCalculus R hSA φ u) := by
  have hi := integrable_boundedBorel φ
    (coordinateSumMeasure R hSA ((spectralUnitary R hSA).symm u))
  rw [scalarMeasure_eq_coordinateSumMeasure R hSA u, coordinateSumMeasure, integral_sum_measure hi,
    ← (spectralUnitary R hSA).symm.inner_map_map u (borelFunctionalCalculus R hSA φ u),
    borelFunctionalCalculus_coordinates, lp.inner_eq_tsum]
  apply tsum_congr
  intro i
  rw [squaredCoordinateMeasure_integral_borel]
  exact (fiberMultiplier_inner_self R hSA (i : H) φ _).symm

/-- Genuine positivity from pointwise real nonnegativity, with no positive
operator premise. Real-valuedness is written as the star-fixed condition. -/
theorem borelFunctionalCalculus_positive
    (φ : BoundedBorelFunction (ResolventSpectrum R))
    (hreal : ∀ t, star (φ t) = φ t) (hpos : ∀ t, 0 ≤ (φ t).re) :
    (borelFunctionalCalculus R hSA φ).IsPositive := by
  have hs := borelFunctionalCalculus_selfAdjoint R hSA φ hreal
  apply ContinuousLinearMap.isPositive_def'.mpr
  refine ⟨hs, ?_⟩
  intro u
  change 0 ≤ (inner ℂ (borelFunctionalCalculus R hSA φ u) u).re
  rw [hs.isSymmetric u u, ← borelFunctionalCalculus_integral,
    ← integral_re (integrable_boundedBorel φ (scalarMeasure R hSA u))]
  exact integral_nonneg hpos

theorem borelFunctionalCalculus_mono
    (φ ψ : BoundedBorelFunction (ResolventSpectrum R))
    (hφ : ∀ t, star (φ t) = φ t) (hψ : ∀ t, star (ψ t) = ψ t)
    (hle : ∀ t, (φ t).re ≤ (ψ t).re) :
    borelFunctionalCalculus R hSA φ ≤ borelFunctionalCalculus R hSA ψ := by
  apply (ContinuousLinearMap.le_def _ _).mpr
  rw [← borelFunctionalCalculus_sub]
  apply borelFunctionalCalculus_positive
  · intro t
    change star (ψ t - φ t) = ψ t - φ t
    rw [star_sub, hψ t, hφ t]
  · intro t
    change 0 ≤ (ψ t - φ t).re
    rw [Complex.sub_re]
    exact sub_nonneg.mpr (hle t)

/-- Exact scalar spectral-measure transport under every bounded Borel
function, established through projection norms and actual multiplication. -/
theorem scalarMeasure_borelFunctionalCalculus
    (φ : BoundedBorelFunction (ResolventSpectrum R)) (u : H) :
    scalarMeasure R hSA (borelFunctionalCalculus R hSA φ u) =
      (scalarMeasure R hSA u).withDensity (fun t => ENNReal.ofReal (‖φ t‖ ^ 2)) := by
  apply Measure.ext
  intro B hB
  rw [scalarMeasure_eq_projection_norm_square R hSA _ B hB]
  have hprod : borelFunctionalCalculus R hSA ((BoundedBorelFunction.indicator B hB).mul φ) u =
      globalBorelProjection R hSA B hB (borelFunctionalCalculus R hSA φ u) := by
    rw [borelFunctionalCalculus_mul, borelFunctionalCalculus_indicator]
    rfl
  rw [← hprod, borelFunctionalCalculus_norm_square]
  have hfun : (fun t => ‖(BoundedBorelFunction.indicator B hB).mul φ t‖ ^ 2) =
      B.indicator (fun t => ‖φ t‖ ^ 2) := by
    funext t
    by_cases ht : t ∈ B <;> simp [BoundedBorelFunction.mul, BoundedBorelFunction.indicator, ht]
  rw [hfun, integral_indicator hB, withDensity_apply _ hB]
  exact ofReal_integral_eq_lintegral_ofReal
    (integrable_norm_square φ (scalarMeasure R hSA u)).integrableOn
    (Filter.Eventually.of_forall fun t => sq_nonneg ‖φ t‖)

theorem scalarMeasure_borelFunctionalCalculus_on
    (φ : BoundedBorelFunction (ResolventSpectrum R)) (u : H)
    (B : Set (ResolventSpectrum R)) (hB : MeasurableSet B) :
    scalarMeasure R hSA (borelFunctionalCalculus R hSA φ u) B =
      ∫⁻ t in B, ENNReal.ofReal (‖φ t‖ ^ 2) ∂scalarMeasure R hSA u := by
  rw [scalarMeasure_borelFunctionalCalculus, withDensity_apply _ hB]

end
end ImbalancedChen.Part3.GenericBoundedBorelScalarTransport20261025a