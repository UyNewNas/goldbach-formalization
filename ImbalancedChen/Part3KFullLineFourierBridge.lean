import ImbalancedChen.Part3ImaginaryOrderKPositiveAxis
import ImbalancedChen.Part3ActualKProfileLp
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
SOURCEONLY, 2026-10-24. UNCOMPILED; no acceptance credit.

The `Part3ActualKProfileLp` import is a future-import staging dependency on the
sibling source-only module. This file proves the pointwise transform identity
from Mathlib's `𝓕` integral and the actual positive-axis definition of
`imaginaryOrderK`. In Mathlib's convention the phase is `exp (-2πiuξ)`.
The factor two comes from reflecting the negative half-axis, and the sine
terms cancel in the sum of the two phases.
-/

namespace ImbalancedChen.Part3.KFullLineFourierBridgeSourceOnly

noncomputable section

open MeasureTheory FourierTransform
open scoped FourierTransform Real
open ImaginaryOrderKBesselSourceOnly
open P3ActualKProfileLpSourceOnly

/-- The actual even, full-line profile. The sibling Lp module proves its L1
and L2 membership for positive `q`. -/
abbrev kEvenProfile (q : ℝ) : ℝ → ℂ := evenLaplaceProfile q

theorem kEvenProfile_neg (q u : ℝ) :
    kEvenProfile q (-u) = kEvenProfile q u := by
  exact evenLaplaceProfile_even q u

theorem kEvenProfile_integrable {q : ℝ} (hq : 0 < q) :
    Integrable (kEvenProfile q) := by
  exact evenLaplaceProfile_integrable hq

/-- Pair the Fourier phases at `u` and `-u`. This is the explicit odd-sine
cancellation; the identity is pointwise and does not use a transform theorem. -/
private theorem paired_phase (g : ℝ → ℂ) (heven : ∀ u, g (-u) = g u)
    (ξ u : ℝ) :
    Complex.exp (((-2 * π * (-u) * ξ : ℝ) : ℂ) * Complex.I) * g (-u) +
      Complex.exp (((-2 * π * u * ξ : ℝ) : ℂ) * Complex.I) * g u =
        (2 : ℂ) * (Real.cos (2 * π * u * ξ) : ℂ) * g u := by
  rw [heven u]
  have hplus : ((-2 * π * (-u) * ξ : ℝ) : ℂ) =
      ((2 * π * u * ξ : ℝ) : ℂ) := by
    push_cast
    ring
  have hminus : ((-2 * π * u * ξ : ℝ) : ℂ) =
      -((2 * π * u * ξ : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hplus, hminus, Complex.ofReal_cos, Complex.two_cos]
  ring

/-- The real part of the paired Fourier phase is precisely the existing
positive-axis K integrand, including its order `2it` normalization. -/
private theorem cosine_profile_eq_kIntegrand (q ξ u : ℝ) :
    (Real.cos (2 * π * u * ξ) : ℂ) * kEvenProfile q u =
      (kIntegrand (π * ξ) q u : ℂ) := by
  simp only [kEvenProfile, evenLaplaceProfile, kIntegrand, ← Complex.ofReal_mul]
  congr 1
  ring

/-- Fourier transform of any integrable, even, complex-valued function on
the real line, in Mathlib's `exp (-2πiuξ)` convention. -/
theorem fourier_even_eq_cosine (g : ℝ → ℂ) (hg : Integrable g)
    (heven : ∀ u, g (-u) = g u) (ξ : ℝ) :
    𝓕 g ξ = (2 : ℂ) *
      ∫ u in Set.Ioi (0 : ℝ), (Real.cos (2 * π * u * ξ) : ℂ) * g u := by
  let F : ℝ → ℂ := fun u =>
    Complex.exp (((-2 * π * u * ξ : ℝ) : ℂ) * Complex.I) * g u
  have hF : Integrable F := by
    have h := (Real.fourierIntegral_convergent_iff
      (f := g) ξ).2 hg
    simpa [F, Circle.smul_def, Real.fourierChar_apply,
      mul_neg, neg_mul, mul_assoc, smul_eq_mul] using h
  have hLeft : IntegrableOn F (Set.Iic (0 : ℝ)) := hF.integrableOn
  have hRight : IntegrableOn F (Set.Ioi (0 : ℝ)) := hF.integrableOn
  have hReflected : IntegrableOn (fun u : ℝ => F (-u)) (Set.Ioi 0) :=
    hF.comp_neg.integrableOn
  have hReflection :
      (∫ u in Set.Iic (0 : ℝ), F u) =
        ∫ u in Set.Ioi (0 : ℝ), F (-u) := by
    simpa only [neg_zero] using
      (integral_comp_neg_Ioi (0 : ℝ) F).symm
  calc
    𝓕 g ξ = ∫ u : ℝ, F u := by
      simpa only [F, smul_eq_mul] using
        (Real.fourier_real_eq_integral_exp_smul g ξ)
    _ = (∫ u in Set.Iic (0 : ℝ), F u) +
          ∫ u in Set.Ioi (0 : ℝ), F u :=
        (integral_Iic_add_Ioi hLeft hRight).symm
    _ = (∫ u in Set.Ioi (0 : ℝ), F (-u)) +
          ∫ u in Set.Ioi (0 : ℝ), F u := by rw [hReflection]
    _ = ∫ u in Set.Ioi (0 : ℝ), (F (-u) + F u) :=
        (integral_add hReflected hRight).symm
    _ = ∫ u in Set.Ioi (0 : ℝ),
          (2 : ℂ) * (Real.cos (2 * π * u * ξ) : ℂ) * g u := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro u
      dsimp only [F]
      exact paired_phase g heven ξ u
    _ = (2 : ℂ) *
          ∫ u in Set.Ioi (0 : ℝ), (Real.cos (2 * π * u * ξ) : ℂ) * g u := by
      simp_rw [mul_assoc]
      rw [integral_const_mul]

/-- The same generic identity with the frequency expressed in K-order
units. This is the interface for a packet's actual even Laplace profile. -/
theorem cosine_integral_eq_half_fourier (g : ℝ → ℂ) (hg : Integrable g)
    (heven : ∀ u, g (-u) = g u) (t : ℝ) :
    (∫ u in Set.Ioi (0 : ℝ), (Real.cos (2 * t * u) : ℂ) * g u) =
      (1 / 2 : ℂ) * 𝓕 g (t / π) := by
  have hangle (u : ℝ) : 2 * π * u * (t / π) = 2 * t * u := by
    field_simp [Real.pi_ne_zero]
    ring
  have h := fourier_even_eq_cosine g hg heven (t / π)
  simp_rw [hangle] at h
  rw [h]
  ring

/-- Actual pointwise Fourier identification, obtained by specializing the
generic split to the real even exponential profile and the existing K
integrand. -/
theorem fourier_kEvenProfile_eq (q ξ : ℝ) (hq : 0 < q) :
    𝓕 (kEvenProfile q) ξ =
      (2 : ℂ) * (imaginaryOrderK (π * ξ) q : ℂ) := by
  rw [fourier_even_eq_cosine (kEvenProfile q)
    (kEvenProfile_integrable hq) (kEvenProfile_neg q) ξ]
  congr 1
  calc
    (∫ u in Set.Ioi (0 : ℝ),
        (Real.cos (2 * π * u * ξ) : ℂ) * kEvenProfile q u) =
      ∫ u in Set.Ioi (0 : ℝ), (kIntegrand (π * ξ) q u : ℂ) := by
        apply integral_congr_ae
        apply Filter.Eventually.of_forall
        intro u
        exact cosine_profile_eq_kIntegrand q ξ u
    _ = (imaginaryOrderK (π * ξ) q : ℂ) := by
      rw [integral_ofReal]
      rfl

/-- Frequency-rescaled inverse statement; `π` is exactly the Mathlib
Fourier-to-order conversion factor. -/
theorem imaginaryOrderK_eq_half_fourier (t q : ℝ) (hq : 0 < q) :
    (imaginaryOrderK t q : ℂ) =
      (1 / 2 : ℂ) * 𝓕 (kEvenProfile q) (t / π) := by
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  rw [fourier_kEvenProfile_eq q (t / π) hq]
  have harg : π * (t / π) = t := by field_simp [hπ]
  rw [harg]
  ring

end
end ImbalancedChen.Part3.KFullLineFourierBridgeSourceOnly
