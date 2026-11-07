import ImbalancedChen.Part3GammaNativeEigenBorelLocalization
import ImbalancedChen.Part3GenericGlobalProjectionScalarConsistency
import Mathlib.MeasureTheory.Measure.Dirac

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The ORIGINAL actual Gamma Laplace scalar measure of an actual native
eigenvector is its exact norm-square Dirac atom at the actual eigenvalue.
This uses the existing native-graph Borel localization and native RMK
projection norm identity, rather than assuming spectral localization.
It also proves mixed Borel orthogonality for distinct actual eigenvalues.
No cusp completeness or automorphic Plancherel normalization is asserted.
-/
namespace ImbalancedChen.Part3.GammaNativeEigenScalarAtom20261026b
noncomputable section
open Set MeasureTheory
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualWeakRieszResolvent20261025a
open Gamma0ActualFriedrichsOperator20261025a Gamma0ActualUnboundedScalarMeasure20261025a
open GenericResolventScalarMeasure20261025a GenericResolventUnboundedScalarMeasure20261025a
open GenericGlobalBorelProjection20261025a GenericGlobalProjectionScalarConsistency20261025a
open GammaMeanCenteredScalarMeasure20261026b GammaNativeEigenBorelLocalization20261026b

/-- The measure is the ORIGINAL unbounded scalar measure of the given
physical vector, not a newly declared measure on eigenvalue labels. -/
theorem actualLaplaceMeasure_apply_eq_projection_norm_square (N : ℕ) [NeZero N]
    (u : QuotientL2 N) (B : Set ℝ) (hB : MeasurableSet B) :
    actualLaplaceMeasure N u B = ENNReal.ofReal (‖actualLaplaceBorelProjection N B hB u‖^2) := by
  change ((scalarMeasure (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N) u).map
      (spectralLambda (actualGammaResolvent N))) B = _
  rw [Measure.map_apply (measurable_spectralLambda (actualGammaResolvent N)) hB]
  exact scalarMeasure_eq_projection_norm_square (actualGammaResolvent N)
    (actualGammaResolvent_selfAdjoint N) u _ ((measurable_spectralLambda (actualGammaResolvent N)) hB)

theorem actual_native_eigen_scalar_measure_eq_atom (N : ℕ) [NeZero N]
    (u : QuotientL2 N) (λ : ℝ)
    (hu : (u,(λ : ℂ) • u) ∈ (actualGammaFriedrichs N).graph) :
    actualLaplaceMeasure N u = ENNReal.ofReal (‖u‖^2) • Measure.dirac λ := by
  apply Measure.ext
  intro B hB
  rw [actualLaplaceMeasure_apply_eq_projection_norm_square N u B hB,
    actual_native_eigenvector_borel_apply N u λ hu B hB]
  by_cases hλ : λ ∈ B <;> simp [hλ, Measure.smul_apply]

/-- Distinct actual native eigenvalues give genuine spectral
orthogonality, including every original real Borel projection. -/
theorem actual_native_distinct_eigenvectors_borel_mixed_zero (N : ℕ) [NeZero N]
    (u v : QuotientL2 N) (λ η : ℝ)
    (hu : (u,(λ : ℂ) • u) ∈ (actualGammaFriedrichs N).graph)
    (hv : (v,(η : ℂ) • v) ∈ (actualGammaFriedrichs N).graph) (hλη : λ ≠ η)
    (B : Set ℝ) (hB : MeasurableSet B) :
    inner ℂ (actualLaplaceBorelProjection N B hB u) v = 0 := by
  have hi : inner ℂ u v = 0 := by
    have hs : inner ℂ (actualLaplaceBorelProjection N {λ} (measurableSet_singleton λ) u) v =
        inner ℂ u (actualLaplaceBorelProjection N {λ} (measurableSet_singleton λ) v) :=
      globalBorelProjection_inner (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N)
        _ ((measurable_spectralLambda (actualGammaResolvent N)) (measurableSet_singleton λ)) u v
    rw [actual_native_eigenvector_borel_apply N u λ hu,
      actual_native_eigenvector_borel_apply N v η hv] at hs
    simpa only [mem_singleton_iff, if_pos rfl, if_neg (Ne.symm hλη), inner_zero_right] using hs
  rw [actual_native_eigenvector_borel_apply N u λ hu]
  split_ifs
  · exact hi
  · exact inner_zero_left _

end
end ImbalancedChen.Part3.GammaNativeEigenScalarAtom20261026b
