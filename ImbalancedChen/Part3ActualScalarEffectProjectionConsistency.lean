import ImbalancedChen.Part3GenericGlobalProjectionScalarConsistency
import ImbalancedChen.Part3ActualScalarEffectAdditivity

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
The previously constructed actual polarized effects agree with the actual
bounded-resolvent global Borel projections. This is proved by native scalar
measure uniqueness followed by equality of all diagonal coefficients.
Consequently the effects are idempotent and multiply by set intersection.
No PVM, representation, idempotence, or projection-law premise is introduced.
This does not identify an automorphic or Kuznetsov spectral decomposition.
-/
namespace ImbalancedChen.Part3.ActualScalarEffectProjectionConsistency20261025a
noncomputable section
open MeasureTheory
open ImbalancedChen.Part3
open MaassFiniteCoreL2Graph20261025a
open ActualCompletedEnergyResolvent20261025a
open GenericGlobalBorelProjection20261025a
open GenericGlobalProjectionScalarConsistency20261025a
open ActualScalarPositiveOperator20261025a
open ActualScalarEffectAdditivity20261025a

abbrev ActualSpectrum := ActualResolventScalarMeasure20261025a.ResolventSpectrum

/-- The separately named concrete and generic RMK measures are the same
measure: their real CFC tests are definitionally the same native CFC. -/
theorem actual_scalarMeasure_eq_generic (u : HyperbolicL2) :
    ActualResolventScalarMeasure20261025a.scalarMeasure u =
      GenericResolventScalarMeasure20261025a.scalarMeasure
        actualWeakResolvent actualWeakResolvent_selfAdjoint u := by
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro φ
  rw [ActualResolventScalarMeasure20261025a.scalarMeasure_integral u φ.toContinuousMap,
    GenericResolventScalarMeasure20261025a.scalarMeasure_integral
      actualWeakResolvent actualWeakResolvent_selfAdjoint u φ.toContinuousMap]
  rfl

abbrev actualGlobalProjection (B : Set ActualSpectrum) (hB : MeasurableSet B) :
    HyperbolicL2 →L[ℂ] HyperbolicL2 :=
  globalBorelProjection actualWeakResolvent actualWeakResolvent_selfAdjoint B hB

/-- Equality is derived from the actual diagonal measure, rather than
postulated as a spectral-representation contract. -/
theorem spectralEffect_eq_actualGlobalProjection (B : Set ActualSpectrum)
    (hB : MeasurableSet B) : spectralEffect B = actualGlobalProjection B hB := by
  apply operator_eq_of_diagonal
  intro u
  rw [spectralEffect_diagonal]
  change (ActualScalarMeasureQuadratic20261025a.spectralQuadratic B u : ℂ) =
    inner ℂ (globalBorelProjection actualWeakResolvent actualWeakResolvent_selfAdjoint B hB u) u
  rw [globalBorelProjection_diagonal]
  change ((ActualResolventScalarMeasure20261025a.scalarMeasure u).real B : ℂ) = _
  rw [actual_scalarMeasure_eq_generic]

/-- The formerly positive-effect-only construction is now a projection
on every measurable set by its identification with the constructed P_B. -/
theorem spectralEffect_idempotent (B : Set ActualSpectrum) (hB : MeasurableSet B) :
    (spectralEffect B).comp (spectralEffect B) = spectralEffect B := by
  rw [spectralEffect_eq_actualGlobalProjection B hB]
  exact globalBorelProjection_idempotent actualWeakResolvent actualWeakResolvent_selfAdjoint B hB

theorem spectralEffect_comp_inter (B C : Set ActualSpectrum)
    (hB : MeasurableSet B) (hC : MeasurableSet C) :
    (spectralEffect B).comp (spectralEffect C) = spectralEffect (B ∩ C) := by
  rw [spectralEffect_eq_actualGlobalProjection B hB,
    spectralEffect_eq_actualGlobalProjection C hC,
    spectralEffect_eq_actualGlobalProjection (B ∩ C) (hB.inter hC)]
  exact globalBorelProjection_comp_inter actualWeakResolvent actualWeakResolvent_selfAdjoint
    B C hB hC

theorem spectralEffect_comp_eq_zero_of_disjoint (B C : Set ActualSpectrum)
    (hB : MeasurableSet B) (hC : MeasurableSet C) (hBC : Disjoint B C) :
    (spectralEffect B).comp (spectralEffect C) = 0 := by
  rw [spectralEffect_comp_inter B C hB hC,
    Set.disjoint_iff_inter_eq_empty.mp hBC, spectralEffect_empty]

theorem actual_scalarMeasure_eq_effect_norm_square (u : HyperbolicL2)
    (B : Set ActualSpectrum) (hB : MeasurableSet B) :
    ActualResolventScalarMeasure20261025a.scalarMeasure u B =
      ENNReal.ofReal (‖spectralEffect B u‖ ^ 2) := by
  rw [actual_scalarMeasure_eq_generic, spectralEffect_eq_actualGlobalProjection B hB]
  exact scalarMeasure_eq_projection_norm_square
    actualWeakResolvent actualWeakResolvent_selfAdjoint u B hB

end
end ImbalancedChen.Part3.ActualScalarEffectProjectionConsistency20261025a