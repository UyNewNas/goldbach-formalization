import ImbalancedChen.Part3GenericGlobalScalarMeasureConsistency
import ImbalancedChen.Part3GenericGlobalBorelProjection

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
The constructed global Borel projection has exactly the native RMK scalar
measure as its squared norm and diagonal coefficient. Every measure identity
is obtained from the preceding all-continuous CFC and uniqueness argument.
-/
namespace ImbalancedChen.Part3.GenericGlobalProjectionScalarConsistency20261025a
noncomputable section
open MeasureTheory
open ImbalancedChen.Part3.GenericResolventScalarMeasure20261025a
open ImbalancedChen.Part3.GenericResolventCyclicL2Representation20261025a
open ImbalancedChen.Part3.GenericResolventGlobalSpectralAssembly20261025a
open ImbalancedChen.Part3.GenericCyclicBorelProjection20261025a
open ImbalancedChen.Part3.GenericGlobalBorelProjection20261025a
open ImbalancedChen.Part3.GenericGlobalScalarMeasureConsistency20261025a

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R)

theorem squaredCoordinateMeasure_borel (f : H) (ξ : ScalarL2 R hSA f)
    (B : Set (ResolventSpectrum R)) (hB : MeasurableSet B) :
    squaredCoordinateMeasure R hSA f ξ B =
      ENNReal.ofReal (‖borelMultiplier R hSA f B hB ξ‖ ^ 2) := by
  rw [← squaredCoordinateMeasure_univ R hSA f (borelMultiplier R hSA f B hB ξ)]
  unfold squaredCoordinateMeasure
  rw [withDensity_apply _ hB, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  symm
  calc
    _ = ∫⁻ t, B.indicator (fun t => ENNReal.ofReal (‖ξ t‖ ^ 2)) t
        ∂scalarMeasure R hSA f := by
      apply lintegral_congr_ae
      filter_upwards [borelMultiplier_coe_ae R hSA f B hB ξ] with t ht
      rw [ht]
      by_cases htB : t ∈ B <;> simp [htB]
    _ = _ := lintegral_indicator hB _

theorem spectralSum_norm_square_tsum (ξ : SpectralSum R hSA) :
    (∑' i : SpectralIndex R hSA, ‖ξ i‖ ^ 2) = ‖ξ‖ ^ 2 := by
  simpa using (lp.hasSum_norm (by norm_num : 0 < (2 : ℝ≥0∞).toReal) ξ).tsum_eq

/-- Exact ENNReal statement, avoiding an implicit finiteness convention. -/
theorem scalarMeasure_eq_projection_norm_square (u : H)
    (B : Set (ResolventSpectrum R)) (hB : MeasurableSet B) :
    scalarMeasure R hSA u B =
      ENNReal.ofReal (‖globalBorelProjection R hSA B hB u‖ ^ 2) := by
  rw [scalarMeasure_eq_coordinateSumMeasure, coordinateSumMeasure, Measure.sum_apply _ hB]
  simp_rw [squaredCoordinateMeasure_borel R hSA _ _ B hB]
  rw [globalBorelProjection_apply, (spectralUnitary R hSA).norm_map]
  change (∑' i : SpectralIndex R hSA,
      ENNReal.ofReal (‖diagonalBorel R hSA B hB ((spectralUnitary R hSA).symm u) i‖ ^ 2)) = _
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _)
    (spectralSum_norm_square_summable R hSA
      (diagonalBorel R hSA B hB ((spectralUnitary R hSA).symm u))),
    spectralSum_norm_square_tsum]

theorem scalarMeasure_real_eq_projection_norm_square (u : H)
    (B : Set (ResolventSpectrum R)) (hB : MeasurableSet B) :
    (scalarMeasure R hSA u).real B = ‖globalBorelProjection R hSA B hB u‖ ^ 2 := by
  change (scalarMeasure R hSA u B).toReal = _
  rw [scalarMeasure_eq_projection_norm_square, ENNReal.toReal_ofReal (sq_nonneg _)]

/-- The orientation matches the first-slot convention of polarized effects. -/
theorem globalBorelProjection_diagonal (u : H)
    (B : Set (ResolventSpectrum R)) (hB : MeasurableSet B) :
    inner ℂ (globalBorelProjection R hSA B hB u) u =
      ((scalarMeasure R hSA u).real B : ℂ) := by
  have hid : globalBorelProjection R hSA B hB (globalBorelProjection R hSA B hB u) =
      globalBorelProjection R hSA B hB u :=
    congrArg (fun T : H →L[ℂ] H => T u) (globalBorelProjection_idempotent R hSA B hB)
  have hi := globalBorelProjection_inner R hSA B hB
    (globalBorelProjection R hSA B hB u) u
  rw [hid, inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow] at hi
  rw [scalarMeasure_real_eq_projection_norm_square]
  exact hi

end
end ImbalancedChen.Part3.GenericGlobalProjectionScalarConsistency20261025a