import ImbalancedChen.Part3KFullLineFourierBridge
import ImbalancedChen.Part3KProfileSchwartz
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic

/-!
SOURCEONLY, 2026-10-24. UNCOMPILED; no acceptance credit.

Future imports `Part3KFullLineFourierBridge` and `Part3KProfileSchwartz`
refer to sibling staged sources. This module proves the genuine full-order
cosine inversion of the existing positive-axis `imaginaryOrderK` integral.
Its Fourier inversion input is Mathlib's Schwartz Fourier pair applied to the
actual `exp (-q*cosh u)` profile, not an assumed K inversion identity.
-/

namespace ImbalancedChen.Part3.KCosineInversionSourceOnly

noncomputable section

open MeasureTheory FourierTransform
open scoped FourierTransform Real
open ImbalancedChen.Part3.KFullLineFourierBridgeSourceOnly
open ImbalancedChen.Part3.KProfileSchwartzSourceOnly
open ImbalancedChen.Part3.ImaginaryOrderKBesselSourceOnly
open ImbalancedChen.Part3.P3ActualKProfileLpSourceOnly

/-- For an integrable even complex function, the origin is null and the
negative half-axis is the reflected positive half-axis. -/
theorem integral_even_eq_two_Ioi (f : ℝ → ℂ) (hf : Integrable f)
    (heven : ∀ x, f (-x) = f x) :
    (∫ x : ℝ, f x) = (2 : ℂ) * ∫ x in Set.Ioi (0 : ℝ), f x := by
  have hl : IntegrableOn f (Set.Iic (0 : ℝ)) := hf.integrableOn
  have hr : IntegrableOn f (Set.Ioi (0 : ℝ)) := hf.integrableOn
  have hreflect :
      (∫ x in Set.Iic (0 : ℝ), f x) =
        ∫ x in Set.Ioi (0 : ℝ), f (-x) := by
    simpa only [neg_zero] using (integral_comp_neg_Ioi (0 : ℝ) f).symm
  calc
    (∫ x : ℝ, f x) =
        (∫ x in Set.Iic (0 : ℝ), f x) +
          ∫ x in Set.Ioi (0 : ℝ), f x :=
      (integral_Iic_add_Ioi hl hr).symm
    _ = (∫ x in Set.Ioi (0 : ℝ), f (-x)) +
          ∫ x in Set.Ioi (0 : ℝ), f x := by rw [hreflect]
    _ = (∫ x in Set.Ioi (0 : ℝ), f x) +
          ∫ x in Set.Ioi (0 : ℝ), f x := by
      congr 1
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      exact heven
    _ = (2 : ℂ) * ∫ x in Set.Ioi (0 : ℝ), f x := by ring

/-- The Schwartz structure gives genuine L1 integrability of the actual
Fourier transform of the actual K profile. -/
private theorem fourier_kEvenProfile_integrable {q : ℝ} (hq : 0 < q) :
    Integrable (𝓕 (kEvenProfile q)) := by
  have hSch : Integrable
      ((𝓕 (complexProfileSchwartz hq) : SchwartzMap ℝ ℂ) : ℝ → ℂ) :=
    (𝓕 (complexProfileSchwartz hq) : SchwartzMap ℝ ℂ).integrable
  have heq : ((complexProfileSchwartz hq : SchwartzMap ℝ ℂ) : ℝ → ℂ) =
      kEvenProfile q := by
    funext x
    exact complexProfileSchwartz_apply hq x
  simpa only [SchwartzMap.fourier_coe, heq] using hSch

/-- The existing K integral is integrable over the entire real order axis.
The proof uses the Fourier bridge and Schwartz decay, then rescales by π. -/
theorem imaginaryOrderK_integrable_order {q : ℝ} (hq : 0 < q) :
    Integrable (fun t : ℝ => (imaginaryOrderK t q : ℂ)) := by
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have hscale : Integrable (fun t : ℝ => 𝓕 (kEvenProfile q) (t / π)) := by
    have h := (fourier_kEvenProfile_integrable hq).comp_mul_left'
      (inv_ne_zero hπ)
    have harg (t : ℝ) : π⁻¹ * t = t / π := by ring
    simpa only [harg] using h
  have heq : (fun t : ℝ => (imaginaryOrderK t q : ℂ)) =
      fun t => (1 / 2 : ℂ) * 𝓕 (kEvenProfile q) (t / π) := by
    funext t
    exact imaginaryOrderK_eq_half_fourier t q hq
  rw [heq]
  exact hscale.const_mul (1 / 2 : ℂ)

/-- Evenness of the actual Fourier transform follows from the proved K
identification and the already proved evenness of `imaginaryOrderK`. -/
private theorem fourier_kEvenProfile_even {q : ℝ} (hq : 0 < q) (ξ : ℝ) :
    𝓕 (kEvenProfile q) (-ξ) = 𝓕 (kEvenProfile q) ξ := by
  rw [fourier_kEvenProfile_eq q (-ξ) hq,
    fourier_kEvenProfile_eq q ξ hq]
  have harg : π * (-ξ) = -(π * ξ) := by ring
  rw [harg, imaginaryOrderK_neg]

/-- Fourier inversion recovers the even profile from the Fourier transform's
full-line cosine integral. The integrability of this cosine integrand follows
from Schwartz decay and `|cos| ≤ 1`. -/
private theorem integral_fourier_profile_mul_cos {q : ℝ} (hq : 0 < q) (u : ℝ) :
    (∫ ξ : ℝ, 𝓕 (kEvenProfile q) ξ *
      (Real.cos (2 * π * ξ * u) : ℂ)) = kEvenProfile q u := by
  let G : ℝ → ℂ := 𝓕 (kEvenProfile q)
  let H : ℝ → ℂ := fun ξ => G ξ * (Real.cos (2 * π * ξ * u) : ℂ)
  have hG : Integrable G := fourier_kEvenProfile_integrable hq
  have hG_even : ∀ ξ, G (-ξ) = G ξ := fourier_kEvenProfile_even hq
  have hcos_cont : Continuous (fun ξ : ℝ =>
      (Real.cos (2 * π * ξ * u) : ℂ)) := by fun_prop
  have hcos_bound : ∀ᵐ ξ : ℝ ∂volume,
      ‖(Real.cos (2 * π * ξ * u) : ℂ)‖ ≤ 1 :=
    Filter.Eventually.of_forall (fun ξ => by
      simpa [Complex.norm_real, Real.norm_eq_abs] using
        Real.abs_cos_le_one (2 * π * ξ * u))
  have hH : Integrable H := by
    simpa only [H, G, smul_eq_mul] using
      hG.smul_bdd 1 hcos_cont.aestronglyMeasurable hcos_bound
  have hH_even : ∀ ξ, H (-ξ) = H ξ := by
    intro ξ
    have ha : 2 * π * (-ξ) * u = -(2 * π * ξ * u) := by ring
    simp only [H, hG_even ξ, ha, Real.cos_neg]
  have hcont : Continuous (kEvenProfile q) := evenLaplaceProfile_continuous q
  have hInv : 𝓕⁻ (𝓕 (kEvenProfile q)) = kEvenProfile q :=
    hcont.fourierInv_fourier_eq (kEvenProfile_integrable hq) hG
  have hFF : 𝓕 G u = kEvenProfile q u := by
    calc
      𝓕 G u = 𝓕⁻ G (-u) := by
        rw [Real.fourierInv_eq_fourier_neg]
        simp
      _ = kEvenProfile q (-u) := congrFun hInv (-u)
      _ = kEvenProfile q u := kEvenProfile_neg q u
  calc
    (∫ ξ : ℝ, 𝓕 (kEvenProfile q) ξ *
        (Real.cos (2 * π * ξ * u) : ℂ)) = ∫ ξ : ℝ, H ξ := rfl
    _ = (2 : ℂ) * ∫ ξ in Set.Ioi (0 : ℝ), H ξ :=
      integral_even_eq_two_Ioi H hH hH_even
    _ = (2 : ℂ) * ∫ ξ in Set.Ioi (0 : ℝ),
          (Real.cos (2 * π * ξ * u) : ℂ) * G ξ := by
      congr 1
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro ξ
      simp only [H]
      ring
    _ = 𝓕 G u := (fourier_even_eq_cosine G hG hG_even u).symm
    _ = kEvenProfile q u := hFF

/-- The true full-order cosine inversion for the defined `K_{2it}(q)`.
The factor `π/2` is forced by `𝓕 g(t/π) = 2 K(t,q)` and `dt = π dξ`. -/
theorem imaginaryOrderK_cosine_inversion (q u : ℝ) (hq : 0 < q) :
    (∫ t : ℝ, (imaginaryOrderK t q : ℂ) *
      (Real.cos (2 * t * u) : ℂ)) =
        ((π / 2 : ℝ) : ℂ) * kEvenProfile q u := by
  let H : ℝ → ℂ := fun ξ => 𝓕 (kEvenProfile q) ξ *
    (Real.cos (2 * π * ξ * u) : ℂ)
  have hpoint (t : ℝ) :
      (imaginaryOrderK t q : ℂ) * (Real.cos (2 * t * u) : ℂ) =
        (1 / 2 : ℂ) * H (t / π) := by
    rw [imaginaryOrderK_eq_half_fourier t q hq]
    have hangle : 2 * π * (t / π) * u = 2 * t * u := by
      field_simp [Real.pi_ne_zero]
      ring
    simp only [H, hangle]
    ring
  have hscale : (∫ t : ℝ, H (t / π)) =
      (π : ℝ) • ∫ ξ : ℝ, H ξ := by
    simpa only [abs_of_pos Real.pi_pos] using (integral_comp_div H π)
  calc
    (∫ t : ℝ, (imaginaryOrderK t q : ℂ) *
        (Real.cos (2 * t * u) : ℂ)) =
      ∫ t : ℝ, (1 / 2 : ℂ) * H (t / π) := by
        apply integral_congr_ae
        apply Filter.Eventually.of_forall
        exact hpoint
    _ = (1 / 2 : ℂ) * ∫ t : ℝ, H (t / π) := by
      rw [integral_const_mul]
    _ = (1 / 2 : ℂ) * ((π : ℝ) • ∫ ξ : ℝ, H ξ) := by rw [hscale]
    _ = ((π / 2 : ℝ) : ℂ) * kEvenProfile q u := by
      have hH : (∫ ξ : ℝ, H ξ) = kEvenProfile q u :=
        integral_fourier_profile_mul_cos hq u
      rw [hH, Complex.real_smul]
      push_cast
      ring

/-- The same inversion statement displaying the original real exponential
profile rather than its Fourier-facing abbreviation. -/
theorem imaginaryOrderK_cosine_inversion_exp (q u : ℝ) (hq : 0 < q) :
    (∫ t : ℝ, (imaginaryOrderK t q : ℂ) *
      (Real.cos (2 * t * u) : ℂ)) =
        ((π / 2 : ℝ) : ℂ) * (Real.exp (-q * Real.cosh u) : ℂ) := by
  simpa only [kEvenProfile, evenLaplaceProfile] using
    imaginaryOrderK_cosine_inversion q u hq

end
end ImbalancedChen.Part3.KCosineInversionSourceOnly
