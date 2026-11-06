import ImbalancedChen.P3FourierRestrictedBox
import ImbalancedChen.P3FourierAutomaticMeasurability
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
P3.6 / manuscript §4 (F), physical-frequency H-box / SOURCE_ONLY.
UNCOMPILED and KERNEL_UNVERIFIED.

This is the genuine Fourier-transform norm tail, not just the separated
Cauchy-kernel mass. It uses the SAME actual original mixed (doubled S)
family, Euclidean Fourier volume, physical 2*pi cutoff and derivativeD.
The original W_T admission, truncated inversion, full modulus arithmetic
and same-rho PP theorem are not proved by this file.
-/

namespace ImbalancedChen.P3FourierActualBoxTail
noncomputable section

open MeasureTheory
open scoped Classical BigOperators FourierTransform
open P3AffineTransitionJets P3FourierDPointwise
open P3FourierPointCoordinateBridge P3FourierCoordinateIBP
open P3FourierPhysicalMeasureD P3FourierProductFubini
open P3FourierAutomaticMeasurability P3FourierRestrictedBox
open P3FourierBoxTailAlgebra

/-- Genuine Fourier-norm integrability, derived from order-zero actual
mixed integrability and the proved-in-source physical Cauchy majorant.
No independent Fourier-norm measurability hypothesis is imposed. -/
theorem actual_fourier_norm_integrable {d : ℕ}
    (w : Point d → ℝ)
    (hsmooth : ∀ S : Finset (Fin d),
      ContDiff ℝ ((doubled S).length : ℕ∞) (chartLift w))
    (hintegrable : ∀ S : Finset (Fin d), ∀ k : ℕ,
      k ≤ (doubled S).length →
        Integrable (iteratedFDeriv ℝ k (complexChartLift w))) :
    Integrable (fun eta : FourierSpace d =>
      ‖𝓕 (actualMixedFamily w ∅) eta‖) := by
  let D : ℝ := derivativeD d (actualMixedFamily w)
  have hzero : Integrable (complexChartLift w) := by
    simpa using (hintegrable ∅ 0 (by simp))
  have hmeas :
      AEStronglyMeasurable (fun eta : FourierSpace d =>
        ‖𝓕 (actualMixedFamily w ∅) eta‖) :=
    actual_fourier_norm_aestronglyMeasurable w hzero
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
  exact Integrable.mono_nonneg hmajor hmeas
    (Filter.Eventually.of_forall (fun eta => norm_nonneg
      (𝓕 (actualMixedFamily w ∅) eta)))
    (Filter.Eventually.of_forall hpoint)

/-- Actual physical H-box complement integral, with dimension-linear
d/H loss. This is the Fourier numerator (not merely the kernel integral).
The constant D is the original ordered doubled-mixed derivative ledger,
and the integration is over the true Euclidean Fourier Haar measure. -/
theorem actual_fourier_box_tail_bound {d : ℕ}
    (w : Point d → ℝ)
    (hsmooth : ∀ S : Finset (Fin d),
      ContDiff ℝ ((doubled S).length : ℕ∞) (chartLift w))
    (hintegrable : ∀ S : Finset (Fin d), ∀ k : ℕ,
      k ≤ (doubled S).length →
        Integrable (iteratedFDeriv ℝ k (complexChartLift w)))
    (H : ℝ) (hH : 0 < H) :
    (∫ eta in (fourierBox d H)ᶜ,
      ‖𝓕 (actualMixedFamily w ∅) eta‖) ≤
        (d : ℝ) * derivativeD d (actualMixedFamily w) / H := by
  let D : ℝ := derivativeD d (actualMixedFamily w)
  have hD : 0 ≤ D := actual_derivativeD_nonneg w
  have hnorm : Integrable (fun eta : FourierSpace d =>
      ‖𝓕 (actualMixedFamily w ∅) eta‖) :=
    actual_fourier_norm_integrable w hsmooth hintegrable
  have hmajor : Integrable (fun eta : FourierSpace d =>
      D * fourierKernel d eta) :=
    (fourierKernel_integrable d).const_mul D
  have hpoint (eta : FourierSpace d) :
      ‖𝓕 (actualMixedFamily w ∅) eta‖ ≤ D * fourierKernel d eta := by
    calc
      ‖𝓕 (actualMixedFamily w ∅) eta‖ ≤
          D / physicalDenom (physicalFrequency (fun i => eta i)) :=
        actual_mixed_physical_decay w hsmooth hintegrable eta
      _ = D * fourierKernel d eta := by
        rw [div_eq_mul_inv, ← fourierKernel_eq_inverse_denom]
  have hrestricted :
      (∫ eta in (fourierBox d H)ᶜ,
        ‖𝓕 (actualMixedFamily w ∅) eta‖) ≤
      ∫ eta in (fourierBox d H)ᶜ,
        D * fourierKernel d eta :=
    setIntegral_mono_on hnorm.integrableOn hmajor.integrableOn
      (fourierBox_measurable d H).compl
      (fun eta _ => hpoint eta)
  calc
    (∫ eta in (fourierBox d H)ᶜ,
      ‖𝓕 (actualMixedFamily w ∅) eta‖) ≤
        ∫ eta in (fourierBox d H)ᶜ,
          D * fourierKernel d eta := hrestricted
    _ = D * separatedBoxMassLoss d H := by
      rw [integral_const_mul, fourierBox_complement_mass d H hH.le]
    _ ≤ (d : ℝ) * D / H :=
      separatedBoxMassLoss_budget d hH hD

/-- Explicit cutoff payment for the ACTUAL Fourier norm tail. The cutoff
condition is a scalar budget inequality, not a PP discrepancy hypothesis.
Neither W_T family admission nor the finite arithmetic modulus sum is
contained in this statement. -/
theorem actual_fourier_box_tail_spend {d : ℕ}
    (w : Point d → ℝ)
    (hsmooth : ∀ S : Finset (Fin d),
      ContDiff ℝ ((doubled S).length : ℕ∞) (chartLift w))
    (hintegrable : ∀ S : Finset (Fin d), ∀ k : ℕ,
      k ≤ (doubled S).length →
        Integrable (iteratedFDeriv ℝ k (complexChartLift w)))
    (H eps : ℝ) (hH : 0 < H)
    (hcut : (d : ℝ) * derivativeD d (actualMixedFamily w) ≤ eps * H) :
    (∫ eta in (fourierBox d H)ᶜ,
      ‖𝓕 (actualMixedFamily w ∅) eta‖) ≤ eps := by
  exact (actual_fourier_box_tail_bound w hsmooth hintegrable H hH).trans
    ((div_le_iff₀ hH).mpr hcut)

end
end ImbalancedChen.P3FourierActualBoxTail
