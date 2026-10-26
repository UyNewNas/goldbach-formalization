import ImbalancedChen.Part3GlobalFrickeParityNativeCalculus
import ImbalancedChen.Part3GenericGlobalProjectionScalarConsistency

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED / ZERO FORMAL CREDIT.

The actual global bounded-Borel model ALREADY exists: its unitary and
projectors are constructed in GenericGlobalBorelProjection, and the
projector/native-RMK diagonal identity is proved independently in
GenericGlobalProjectionScalarConsistency. No replacement projector or
spectral model is introduced. Actual continuous-CFC Fricke commutation
and Hilbert isometry imply native scalar-measure invariance by genuine
continuous-test uniqueness. The existing Borel diagonal identity and
complex polarization then prove actual projector commutation.
-/

noncomputable section

namespace ImbalancedChen.Part3.GlobalFrickeBorelProjectionCommutation20261026b

open Set MeasureTheory
open ImbalancedChen.Part3.ActualHeckeSecondL220261026b
open ImbalancedChen.Part3.GlobalFrickeHilbertInvolution20261026b
open ImbalancedChen.Part3.GlobalFrickeFriedrichsIntertwining20261026b
open ImbalancedChen.Part3.GlobalFrickeParityNativeCalculus20261026b
open ImbalancedChen.Part3.Gamma0ActualSmoothQuotientCore20261025a
open ImbalancedChen.Part3.Gamma0ActualWeakRieszResolvent20261025a
open ImbalancedChen.Part3.GenericResolventScalarMeasure20261025a
open ImbalancedChen.Part3.GenericGlobalBorelProjection20261025a
open ImbalancedChen.Part3.GenericGlobalProjectionScalarConsistency20261025a

/-- Invariance of the actual native RMK measure is proved from EVERY
continuous compactly supported test; it is not a spectral hypothesis. -/
theorem actualResolventScalarMeasure_fricke (N : ℕ) [NeZero N] (hN : 0 < N)
    (f : QuotientL2 N) :
    scalarMeasure (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N) (frickeL2 N hN f) =
      scalarMeasure (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N) f := by
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro φ
  calc
    (∫ t, φ t ∂scalarMeasure (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N)
        (frickeL2 N hN f)) =
        (inner ℂ (frickeL2 N hN f)
          (resolventCFC (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N)
            φ.toContinuousMap (frickeL2 N hN f))).re :=
      scalarMeasure_integral _ _ _ φ.toContinuousMap
    _ = (inner ℂ f (resolventCFC (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N)
        φ.toContinuousMap f)).re := by
      rw [← actualRealCFC_fricke N hN φ.toContinuousMap f, (frickeL2 N hN).inner_map_map]
    _ = ∫ t, φ t ∂scalarMeasure (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N) f :=
      (scalarMeasure_integral _ _ _ φ.toContinuousMap).symm

/-- Conjugating the EXISTING true Borel projector has the same complex
diagonal, by the proved actual RMK/projector consistency theorem. -/
theorem conjugate_actualBorel_diagonal (N : ℕ) [NeZero N] (hN : 0 < N)
    (B : Set (ResolventSpectrum (actualGammaResolvent N))) (hB : MeasurableSet B)
    (f : QuotientL2 N) :
    inner ℂ (frickeL2 N hN (globalBorelProjection (actualGammaResolvent N)
      (actualGammaResolvent_selfAdjoint N) B hB (frickeL2 N hN f))) f =
      inner ℂ (globalBorelProjection (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N) B hB f) f := by
  rw [frickeL2_inner_flip, globalBorelProjection_diagonal,
    actualResolventScalarMeasure_fricke, globalBorelProjection_diagonal]

/-- Full operator conjugacy follows by COMPLEX polarization of all
diagonals. No presumed Borel commutation is supplied as a field. -/
theorem conjugate_actualBorel_eq (N : ℕ) [NeZero N] (hN : 0 < N)
    (B : Set (ResolventSpectrum (actualGammaResolvent N))) (hB : MeasurableSet B) :
    (frickeL2 N hN).toContinuousLinearMap.comp
      ((globalBorelProjection (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N) B hB).comp
        (frickeL2 N hN).toContinuousLinearMap) =
      globalBorelProjection (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N) B hB := by
  let P := globalBorelProjection (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N) B hB
  let Q := (frickeL2 N hN).toContinuousLinearMap.comp (P.comp (frickeL2 N hN).toContinuousLinearMap)
  have hd (u : QuotientL2 N) : inner ℂ (Q u) u = inner ℂ (P u) u :=
    conjugate_actualBorel_diagonal N hN B hB u
  have hm (u v : QuotientL2 N) : inner ℂ (Q u) v = inner ℂ (P u) v := by
    rw [inner_map_polarization' Q.toLinearMap u v, inner_map_polarization' P.toLinearMap u v]
    simp only [hd]
  apply ContinuousLinearMap.ext
  intro u
  exact ext_inner_right ℂ (hm u)

/-- The actual bounded Borel projector of the actual quotient resolvent
commutes with literal canonical global Fricke for EVERY Borel set. -/
theorem actualBorel_fricke (N : ℕ) [NeZero N] (hN : 0 < N)
    (B : Set (ResolventSpectrum (actualGammaResolvent N))) (hB : MeasurableSet B)
    (f : QuotientL2 N) :
    frickeL2 N hN (globalBorelProjection (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N) B hB f) =
      globalBorelProjection (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N) B hB (frickeL2 N hN f) := by
  have h := congrArg (fun T : QuotientL2 N →L[ℂ] QuotientL2 N => T (frickeL2 N hN f))
    (conjugate_actualBorel_eq N hN B hB)
  change frickeL2 N hN (globalBorelProjection (actualGammaResolvent N)
    (actualGammaResolvent_selfAdjoint N) B hB (frickeL2 N hN (frickeL2 N hN f))) = _ at h
  simpa only [frickeL2_involutive N hN f] using h

end ImbalancedChen.Part3.GlobalFrickeBorelProjectionCommutation20261026b
