import ImbalancedChen.Part3KCosineInversion
import ImbalancedChen.Part3KHeightSchwartz
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Tactic

/-!
SOURCEONLY, 2026-10-24. UNCOMPILED; no acceptance credit.

`Part3KHeightSchwartz` is a future-import staging dependency on the sibling
source-only object. The full cosine inversion has already fixed the Fourier
transform of the actual K function. This module derives all even polynomial
cosine moments by applying Mathlib's iterated Fourier derivative theorem to
that actual Schwartz K function; no moment or spectral bound is assumed.
-/

namespace ImbalancedChen.Part3.KCosineMomentsSourceOnly

noncomputable section

open MeasureTheory FourierTransform
open scoped FourierTransform Real
open ImbalancedChen.Part3.ImaginaryOrderKBesselSourceOnly
open ImbalancedChen.Part3.KFullLineFourierBridgeSourceOnly
open ImbalancedChen.Part3.KCosineInversionSourceOnly
open ImbalancedChen.Part3.KHeightSchwartzP3SourceOnly

abbrev Kline (q : ℝ) : ℝ → ℂ :=
  fun t => (imaginaryOrderK t q : ℂ)

private theorem Kline_even (q t : ℝ) : Kline q (-t) = Kline q t := by
  simp only [Kline, imaginaryOrderK_neg]

/-- The dual Fourier transform of the actual K integral. The factor π/2
comes from the proved full-order cosine inversion. -/
theorem fourier_imaginaryOrderK (q ξ : ℝ) (hq : 0 < q) :
    𝓕 (Kline q) ξ = ((π / 2 : ℝ) : ℂ) * kEvenProfile q (π * ξ) := by
  have hK : Integrable (Kline q) := imaginaryOrderK_integrable_order hq
  let C : ℝ → ℂ := fun t => Kline q t *
    (Real.cos (2 * π * t * ξ) : ℂ)
  have hcos_cont : Continuous (fun t : ℝ =>
      (Real.cos (2 * π * t * ξ) : ℂ)) := by fun_prop
  have hcos_bound : ∀ᵐ t : ℝ ∂volume,
      ‖(Real.cos (2 * π * t * ξ) : ℂ)‖ ≤ 1 :=
    Filter.Eventually.of_forall (fun t => by
      simpa [Complex.norm_real, Real.norm_eq_abs] using
        Real.abs_cos_le_one (2 * π * t * ξ))
  have hC : Integrable C := by
    simpa only [C, smul_eq_mul] using
      hK.smul_bdd 1 hcos_cont.aestronglyMeasurable hcos_bound
  have hC_even : ∀ t, C (-t) = C t := by
    intro t
    have ha : 2 * π * (-t) * ξ = -(2 * π * t * ξ) := by ring
    simp only [C, Kline_even q t, ha, Real.cos_neg]
  calc
    𝓕 (Kline q) ξ = (2 : ℂ) *
        ∫ t in Set.Ioi (0 : ℝ),
          (Real.cos (2 * π * t * ξ) : ℂ) * Kline q t :=
      fourier_even_eq_cosine (Kline q) hK (Kline_even q) ξ
    _ = (2 : ℂ) * ∫ t in Set.Ioi (0 : ℝ), C t := by
      congr 1
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro t
      simp only [C]
      ring
    _ = ∫ t : ℝ, C t := (integral_even_eq_two_Ioi C hC hC_even).symm
    _ = ((π / 2 : ℝ) : ℂ) * kEvenProfile q (π * ξ) := by
      have hangle (t : ℝ) : 2 * π * t * ξ = 2 * t * (π * ξ) := by ring
      change (∫ t : ℝ, (imaginaryOrderK t q : ℂ) *
        (Real.cos (2 * π * t * ξ) : ℂ)) = _
      simp_rw [hangle]
      exact imaginaryOrderK_cosine_inversion q (π * ξ) hq

/-- Every real polynomial moment of the actual K function is integrable.
This uses its constructed height Schwartz structure. -/
private theorem Kline_weighted_integrable {q : ℝ} (hq : 0 < q) (m : ℕ) :
    Integrable (fun t : ℝ => t ^ m • Kline q t) := by
  have hs : Integrable (fun t : ℝ =>
      ‖t‖ ^ m * ‖kHeightSchwartz q hq t‖) :=
    (kHeightSchwartz q hq).integrable_pow_mul volume m
  have hc : Continuous (fun t : ℝ =>
      t ^ m • kHeightSchwartz q hq t) :=
    (continuous_id.pow m).smul (kHeightSchwartz q hq).continuous
  have hm : AEStronglyMeasurable (fun t : ℝ => t ^ m • Kline q t) := by
    have heq : (fun t : ℝ => t ^ m • Kline q t) =
        fun t => t ^ m • kHeightSchwartz q hq t := by
      funext t
      rw [kHeightSchwartz_apply]
    rw [heq]
    exact hc.aestronglyMeasurable
  apply (integrable_norm_iff hm).2
  simpa only [norm_smul, Real.norm_eq_abs, abs_pow,
    kHeightSchwartz_apply, Kline] using hs

/-- The complex Fourier moment identity for every order, with the exact
Mathlib phase `-2πitξ`. It is the source for the even cosine moments below. -/
theorem imaginaryOrderK_iterated_fourier_moment (q ξ : ℝ) (hq : 0 < q)
    (m : ℕ) :
    𝓕 (fun t : ℝ => (-2 * π * Complex.I * t) ^ m • Kline q t) ξ =
      iteratedDeriv m
        (fun x : ℝ => ((π / 2 : ℝ) : ℂ) * kEvenProfile q (π * x)) ξ := by
  have hweighted : ∀ n : ℕ, n ≤ (⊤ : ℕ∞) →
      Integrable (fun t : ℝ => t ^ n • Kline q t) := by
    intro n _
    exact Kline_weighted_integrable hq n
  have hderiv := Real.iteratedDeriv_fourier
    (f := Kline q) (N := ⊤) (n := m) hweighted (by simp)
  have hdual : 𝓕 (Kline q) =
      (fun x : ℝ => ((π / 2 : ℝ) : ℂ) * kEvenProfile q (π * x)) := by
    funext x
    exact fourier_imaginaryOrderK q x hq
  rw [hdual] at hderiv
  exact (congrFun hderiv ξ).symm

/-- The phase coefficient for the `2n`-th derivative is real:
`(-2πit)^(2n) = (-1)^n (2π)^(2n) t^(2n)`. -/
private theorem even_phase_power (n : ℕ) (t : ℝ) :
    (-2 * π * Complex.I * t) ^ (2 * n) =
      (-1 : ℂ) ^ n * (((2 * π : ℝ) : ℂ) ^ (2 * n)) *
        ((t ^ (2 * n) : ℝ) : ℂ) := by
  have hp : (-2 * π * Complex.I * t) ^ 2 =
      (-1 : ℂ) * (((2 * π : ℝ) : ℂ) ^ 2) * ((t : ℂ) ^ 2) := by
    calc
      (-2 * π * Complex.I * t) ^ 2 =
          (((2 * π : ℝ) : ℂ) ^ 2) * Complex.I ^ 2 * (t : ℂ) ^ 2 := by
        push_cast
        ring
      _ = (-1 : ℂ) * (((2 * π : ℝ) : ℂ) ^ 2) * ((t : ℂ) ^ 2) := by
        rw [Complex.I_sq]
        ring
  calc
    (-2 * π * Complex.I * t) ^ (2 * n) =
        ((-2 * π * Complex.I * t) ^ 2) ^ n := by rw [pow_mul]
    _ = ((-1 : ℂ) * (((2 * π : ℝ) : ℂ) ^ 2) * ((t : ℂ) ^ 2)) ^ n := by
      rw [hp]
    _ = (-1 : ℂ) ^ n * (((2 * π : ℝ) : ℂ) ^ (2 * n)) *
          ((t ^ (2 * n) : ℝ) : ℂ) := by
      rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul]
      push_cast
      ring

/-- Actual even cosine moments, at every order and every physical `u`.
The coefficient is kept on the left, avoiding any division at `n=0` while
retaining the exact Fourier normalization. -/
theorem imaginaryOrderK_even_cosine_moment (q u : ℝ) (hq : 0 < q)
    (n : ℕ) :
    ((-1 : ℂ) ^ n * (((2 * π : ℝ) : ℂ) ^ (2 * n))) *
      (∫ t : ℝ, ((t ^ (2 * n) : ℝ) : ℂ) * Kline q t *
        (Real.cos (2 * t * u) : ℂ)) =
      iteratedDeriv (2 * n)
        (fun x : ℝ => ((π / 2 : ℝ) : ℂ) * kEvenProfile q (π * x))
        (u / π) := by
  let J : ℝ → ℂ := fun t => ((t ^ (2 * n) : ℝ) : ℂ) * Kline q t
  let c : ℂ := (-1 : ℂ) ^ n * (((2 * π : ℝ) : ℂ) ^ (2 * n))
  have hJ : Integrable J := by
    have h := Kline_weighted_integrable hq (2 * n)
    simpa only [J, Complex.real_smul, Complex.ofReal_pow] using h
  have hJ_even : ∀ t, J (-t) = J t := by
    intro t
    have hp : (-t) ^ (2 * n) = t ^ (2 * n) := by
      rw [pow_mul, pow_mul]
      simp
    simp only [J, Kline_even q t, hp]
  have hcos_cont : Continuous (fun t : ℝ =>
      (Real.cos (2 * π * t * (u / π)) : ℂ)) := by fun_prop
  have hcos_bound : ∀ᵐ t : ℝ ∂volume,
      ‖(Real.cos (2 * π * t * (u / π)) : ℂ)‖ ≤ 1 :=
    Filter.Eventually.of_forall (fun t => by
      simpa [Complex.norm_real, Real.norm_eq_abs] using
        Real.abs_cos_le_one (2 * π * t * (u / π)))
  let H : ℝ → ℂ := fun t => J t *
    (Real.cos (2 * π * t * (u / π)) : ℂ)
  have hH : Integrable H := by
    simpa only [H, smul_eq_mul] using
      hJ.smul_bdd 1 hcos_cont.aestronglyMeasurable hcos_bound
  have hH_even : ∀ t, H (-t) = H t := by
    intro t
    have ha : 2 * π * (-t) * (u / π) =
        -(2 * π * t * (u / π)) := by ring
    simp only [H, hJ_even t, ha, Real.cos_neg]
  have hCosFourier :
      (∫ t : ℝ, J t * (Real.cos (2 * π * t * (u / π)) : ℂ)) =
        𝓕 J (u / π) := by
    calc
      (∫ t : ℝ, J t * (Real.cos (2 * π * t * (u / π)) : ℂ)) =
          ∫ t : ℝ, H t := rfl
      _ = (2 : ℂ) * ∫ t in Set.Ioi (0 : ℝ), H t :=
        integral_even_eq_two_Ioi H hH hH_even
      _ = (2 : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
            (Real.cos (2 * π * t * (u / π)) : ℂ) * J t := by
        congr 1
        apply integral_congr_ae
        apply Filter.Eventually.of_forall
        intro t
        simp only [H]
        ring
      _ = 𝓕 J (u / π) :=
        (fourier_even_eq_cosine J hJ hJ_even (u / π)).symm
  have hphase : (fun t : ℝ =>
      (-2 * π * Complex.I * t) ^ (2 * n) • Kline q t) =
        (fun t : ℝ => c * J t) := by
    funext t
    simp only [J, c, smul_eq_mul, even_phase_power]
    ring
  have hFourierConst : 𝓕 (fun t : ℝ => c * J t) (u / π) =
      c * 𝓕 J (u / π) := by
    calc
      𝓕 (fun t : ℝ => c * J t) (u / π) =
          ∫ t : ℝ, Complex.exp (((-2 * π * t * (u / π) : ℝ) : ℂ) *
            Complex.I) * (c * J t) := by
        simpa only [smul_eq_mul] using
          (Real.fourier_real_eq_integral_exp_smul
            (fun t : ℝ => c * J t) (u / π))
      _ = ∫ t : ℝ, c *
          (Complex.exp (((-2 * π * t * (u / π) : ℝ) : ℂ) *
            Complex.I) * J t) := by
        apply integral_congr_ae
        apply Filter.Eventually.of_forall
        intro t
        ring
      _ = c * ∫ t : ℝ, Complex.exp (((-2 * π * t * (u / π) : ℝ) : ℂ) *
            Complex.I) * J t := by rw [integral_const_mul]
      _ = c * 𝓕 J (u / π) := by
        rw [Real.fourier_real_eq_integral_exp_smul]
        simp only [smul_eq_mul]
  have hm := imaginaryOrderK_iterated_fourier_moment q (u / π) hq (2 * n)
  rw [hphase, hFourierConst] at hm
  have hangle (t : ℝ) : 2 * π * t * (u / π) = 2 * t * u := by
    field_simp [Real.pi_ne_zero]
    ring
  change c * (∫ t : ℝ, J t * (Real.cos (2 * t * u) : ℂ)) = _
  simp_rw [← hangle]
  rw [hCosFourier]
  exact hm

end
end ImbalancedChen.Part3.KCosineMomentsSourceOnly
