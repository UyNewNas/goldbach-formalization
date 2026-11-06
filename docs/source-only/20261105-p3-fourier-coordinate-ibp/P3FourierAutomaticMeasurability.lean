import ImbalancedChen.P3FourierProductFubini
import ImbalancedChen.P3FourierRealComplex
import Mathlib.Analysis.Fourier.FourierTransform

/-!
P3.6 / manuscript-internal / SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.

This removes the extra AEStronglyMeasurable hypothesis from the predecessor's
actual Fourier L1 bound. The pinned Mathlib Fourier continuity theorem is
used for the original zero-order doubled mixed family on the SAME Euclidean
space. The input is actual derivative integrability with S=empty, k=0.

The quantitative H-box tail, complete W_T family admission, complete same-rho
modulus sum and the PP conclusion are NOT claimed here.
-/

namespace ImbalancedChen.P3FourierAutomaticMeasurability
noncomputable section

open MeasureTheory
open scoped Classical BigOperators FourierTransform RealInnerProductSpace
open P3AffineTransitionJets P3U5ChartMixedL1Budget
open P3FourierDPointwise P3FourierPointCoordinateBridge
open P3FourierRealComplex P3FourierProductFubini

/-- The empty original ordered doubled derivative is exactly its original
chart weight, complexified. No surrogate weight and no regularity premise. -/
theorem actual_mixed_empty_eq_chart {d : ℕ}
    (w : Point d → ℝ) :
    actualMixedFamily w ∅ = complexChartLift w := by
  funext eta
  change ((mixed (doubled (∅ : Finset (Fin d))) w
    (fun i => eta i) : ℝ) : ℂ) =
    ((w (chartEquiv d eta) : ℝ) : ℂ)
  simp [doubled, mixed, chartEquiv]

/-- Pinned FourierTransform.lean: the genuine Fourier transform of an
integrable function is continuous. No Fourier estimate is assumed. -/
theorem fourier_continuous_of_integrable {d : ℕ}
    (f : FourierSpace d → ℂ) (hf : Integrable f) :
    Continuous (𝓕 f) := by
  exact VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar (innerSL ℝ).continuous₂ hf

/-- Existing order-zero integrability supplies measurability of the norm
of the original Fourier transform, rather than requiring it separately. -/
theorem actual_fourier_norm_aestronglyMeasurable {d : ℕ}
    (w : Point d → ℝ)
    (hzero : Integrable (complexChartLift w)) :
    AEStronglyMeasurable
      (fun eta : FourierSpace d => ‖𝓕 (actualMixedFamily w ∅) eta‖) := by
  have hbase : Integrable (actualMixedFamily w ∅) := by
    rw [actual_mixed_empty_eq_chart]
    exact hzero
  exact (fourier_continuous_of_integrable
    (actualMixedFamily w ∅) hbase).norm.aestronglyMeasurable

/-- REAL finite-dimensional Fourier L1 majorant for the genuine mixed
(doubled S) family. Unlike the predecessor, no standalone Fourier norm
measurability hypothesis is required. All other stated analytic premises
remain; in particular this does not prove admission of every W_T. -/
theorem actual_fourier_L1_no_meas {d : ℕ}
    (w : Point d → ℝ)
    (hsmooth : ∀ S : Finset (Fin d),
      ContDiff ℝ ((doubled S).length : ℕ∞) (chartLift w))
    (hintegrable : ∀ S : Finset (Fin d), ∀ k : ℕ,
      k ≤ (doubled S).length →
        Integrable (iteratedFDeriv ℝ k (complexChartLift w))) :
    (∫ eta : FourierSpace d, ‖𝓕 (actualMixedFamily w ∅) eta‖) ≤
      derivativeD d (actualMixedFamily w) * (1 / 2 : ℝ) ^ d := by
  have hzero : Integrable (complexChartLift w) := by
    simpa using (hintegrable ∅ 0 (by simp))
  have hmeas := actual_fourier_norm_aestronglyMeasurable w hzero
  exact actual_fourier_L1_bound w hsmooth hintegrable hmeas

end
end ImbalancedChen.P3FourierAutomaticMeasurability
