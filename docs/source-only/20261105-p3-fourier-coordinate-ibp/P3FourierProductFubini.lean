import ImbalancedChen.P3FourierPhysicalMeasureD
import ImbalancedChen.P3FourierCauchyAxis
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
P3.6 / manuscript-internal / SOURCE_ONLY / uncompiled / kernel-unverified.

The actual volume on Point d is the finite pi-product of real Lebesgue
volumes. The genuine Point-to-Euclidean Fourier chart was paid in
P3FourierPhysicalMeasureD. This file uses the PINNED Mathlib
integral_fintype_prod_volume_eq_pow / Integrable.fintype_prod
rather than treating the separated product as an integral by definition.

The integrable Cauchy kernel is evaluated at the ACTUAL Mathlib Fourier
frequency eta, i.e. physical xi = 2*pi*eta. The result is (1/2)^d,
including d=0. The final Fourier L1 lemma also consumes the genuine
original 2S Point mixed-derivative D bound, with explicit ordinary
Fourier-norm measurability. No truncation or arithmetic estimate is claimed.
-/

namespace ImbalancedChen.P3FourierProductFubini
noncomputable section

open MeasureTheory
open scoped Classical BigOperators FourierTransform
open P3AffineTransitionJets P3FourierDPointwise
open P3FourierSubsetExpansion P3FourierPointCoordinateBridge
open P3FourierPhysicalMeasureD P3FourierCoordinateIBP
open P3FourierCauchyAxis

/-- Same physical 2*pi phase in every original coordinate; no new W. -/
def pointKernel (d : ℕ) (p : Point d) : ℝ :=
  ∏ i : Fin d, axisKernel (2 * Real.pi * p i)

/-- The true Euclidean Fourier integration space, with its fixed Haar volume. -/
def fourierKernel (d : ℕ) (eta : FourierSpace d) : ℝ :=
  pointKernel d (chartEquiv d eta)

/-- Pinned Haar scaling gives ordinary Lebesgue integrability at 2*pi. -/
theorem scaledAxis_integrable :
    Integrable (fun x : ℝ => axisKernel (2 * Real.pi * x)) := by
  have hc : (2 * Real.pi : ℝ) ≠ 0 := ne_of_gt (by positivity)
  exact (integrable_comp_mul_left_iff axisKernel hc).2 axisKernel_integrable

/-- Actual finite product-measure integrability, including empty products. -/
theorem pointKernel_integrable (d : ℕ) :
    Integrable (pointKernel d) := by
  simpa only [pointKernel] using
    (Integrable.fintype_prod
      (ι := Fin d) (E := ℝ)
      (μ := fun _ : Fin d => (volume : Measure ℝ))
      (f := fun _ : Fin d => fun x : ℝ =>
        axisKernel (2 * Real.pi * x))
      (fun _ => scaledAxis_integrable))

/-- Genuine d-fold Fubini on the Point product volume, not scalar algebra. -/
theorem pointKernel_mass (d : ℕ) :
    (∫ p : Point d, pointKernel d p) = (1 / 2 : ℝ) ^ d := by
  have hf :=
    integral_fintype_prod_volume_eq_pow (ι := Fin d)
      (f := fun x : ℝ => axisKernel (2 * Real.pi * x))
  change (∫ p : Point d, ∏ i : Fin d,
    axisKernel (2 * Real.pi * p i)) = (1 / 2 : ℝ) ^ d
  rw [hf, axisKernel_mathlib_mass, Fintype.card_fin]

/-- The original isometric Point/Fourier chart preserves the ENTIRE
d-dimensional integral, without a Jacobian or an artificial 2^d. -/
theorem fourierKernel_mass (d : ℕ) :
    (∫ eta : FourierSpace d, fourierKernel d eta) =
      (1 / 2 : ℝ) ^ d := by
  calc
    (∫ eta : FourierSpace d, fourierKernel d eta) =
        ∫ p : Point d, pointKernel d p :=
      integral_chart d (pointKernel d)
    _ = (1 / 2 : ℝ) ^ d := pointKernel_mass d

/-- Integrability is transported using the SAME measure-preserving chart. -/
theorem fourierKernel_integrable (d : ℕ) :
    Integrable (fourierKernel d) := by
  exact ((chart_measure_preserving d).integrable_comp_emb
    (chartEquiv d).toHomeomorph.measurableEmbedding).2
      (pointKernel_integrable d)

/-- Equality with the existing full physical denominator (no radial
replacement, no loss of repeated source coordinates). -/
theorem fourierKernel_eq_inverse_denom {d : ℕ}
    (eta : FourierSpace d) :
    fourierKernel d eta =
      (physicalDenom (physicalFrequency (fun i => eta i)))⁻¹ := by
  unfold fourierKernel pointKernel axisKernel
    physicalDenom physicalFrequency
  change (∏ i : Fin d, (1 + (2 * Real.pi * eta i) ^ 2)⁻¹) =
    (∏ i : Fin d, (1 + (2 * Real.pi * eta i) ^ 2))⁻¹
  simp only [Finset.prod_inv_distrib]

/-- True Euclidean-space (not formal separated scalar) inverse-product mass. -/
theorem physical_inverse_denom_mass (d : ℕ) :
    (∫ eta : FourierSpace d,
      (physicalDenom (physicalFrequency (fun i => eta i)))⁻¹) =
      (1 / 2 : ℝ) ^ d := by
  simp_rw [← fourierKernel_eq_inverse_denom]
  exact fourierKernel_mass d

/-- Explicit finite D from the actual original mixed (doubled S) family.
This is nonnegative even before all W_T admissibility is proved. -/
theorem actual_derivativeD_nonneg {d : ℕ} (w : Point d → ℝ) :
    0 ≤ derivativeD d (actualMixedFamily w) := by
  unfold derivativeD
  exact Finset.sum_nonneg (fun S _ =>
    integral_nonneg (fun x => norm_nonneg (actualMixedFamily w S x)))

/-- The Fourier L1 numerator is now a REAL multidimensional integral.
The measurability hypothesis is the ordinary analytic property of the
actual transform, not a desired Fourier bound or PP discrepancy.
The actual smoothness/integrability are precisely the predecessor's
original 2S hypotheses; the quantitative D comes from originalWD. -/
theorem actual_fourier_L1_bound {d : ℕ}
    (w : Point d → ℝ)
    (hsmooth : ∀ S : Finset (Fin d),
      ContDiff ℝ ((doubled S).length : ℕ∞) (chartLift w))
    (hintegrable : ∀ S : Finset (Fin d), ∀ k : ℕ,
      k ≤ (doubled S).length →
        Integrable (iteratedFDeriv ℝ k (complexChartLift w)))
    (hFourierMeas : AEStronglyMeasurable
      (fun eta : FourierSpace d => ‖𝓕 (actualMixedFamily w ∅) eta‖)) :
    (∫ eta : FourierSpace d, ‖𝓕 (actualMixedFamily w ∅) eta‖) ≤
      derivativeD d (actualMixedFamily w) * (1 / 2 : ℝ) ^ d := by
  let D : ℝ := derivativeD d (actualMixedFamily w)
  have hD : 0 ≤ D := actual_derivativeD_nonneg w
  have hpoint (eta : FourierSpace d) :
      ‖𝓕 (actualMixedFamily w ∅) eta‖ ≤ D * fourierKernel d eta := by
    calc
      ‖𝓕 (actualMixedFamily w ∅) eta‖ ≤
          D / physicalDenom (physicalFrequency (fun i => eta i)) :=
        actual_mixed_physical_decay w hsmooth hintegrable eta
      _ = D * fourierKernel d eta := by
        rw [div_eq_mul_inv, ← fourierKernel_eq_inverse_denom]
  have hmajor : Integrable (fun eta : FourierSpace d =>
      D * fourierKernel d eta) :=
    (fourierKernel_integrable d).const_mul D
  have hnorm : Integrable (fun eta : FourierSpace d =>
      ‖𝓕 (actualMixedFamily w ∅) eta‖) :=
    Integrable.mono_nonneg hmajor hFourierMeas
      (Filter.Eventually.of_forall (fun eta =>
        norm_nonneg (𝓕 (actualMixedFamily w ∅) eta)))
      (Filter.Eventually.of_forall hpoint)
  calc
    (∫ eta : FourierSpace d, ‖𝓕 (actualMixedFamily w ∅) eta‖) ≤
        ∫ eta : FourierSpace d, D * fourierKernel d eta :=
      integral_mono hnorm hmajor hpoint
    _ = D * (1 / 2 : ℝ) ^ d := by
      rw [integral_const_mul, fourierKernel_mass]
    _ = derivativeD d (actualMixedFamily w) * (1 / 2 : ℝ) ^ d := rfl

end
end ImbalancedChen.P3FourierProductFubini
