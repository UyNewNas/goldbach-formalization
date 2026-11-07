import ImbalancedChen.Part3KFullLineFourierBridge
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic

/-!
SOURCEONLY, 2026-10-24. UNCOMPILED; no acceptance credit.

The import of `Part3KFullLineFourierBridge` is a future-import staging
dependency on the sibling source-only Fourier bridge. This proves the
positive-definite property of the actual `imaginaryOrderK` in its real order:
the finite quadratic form is exactly an integral of a positive profile times
the squared modulus of a finite exponential polynomial. Individual values
of `imaginaryOrderK` are not assumed nonnegative.
-/

namespace ImbalancedChen.Part3.KPositiveDefiniteSourceOnly

noncomputable section

open MeasureTheory FourierTransform
open scoped FourierTransform Real
open ImbalancedChen.Part3.ImaginaryOrderKBesselSourceOnly
open ImbalancedChen.Part3.KFullLineFourierBridgeSourceOnly
open ImbalancedChen.Part3.P3ActualKProfileLpSourceOnly

private def phase (t u : ℝ) : ℂ :=
  Complex.exp (((2 * t * u : ℝ) : ℂ) * Complex.I)

private def halfProfile (q u : ℝ) : ℂ :=
  (1 / 2 : ℂ) * kEvenProfile q u

private theorem halfProfile_integrable {q : ℝ} (hq : 0 < q) :
    Integrable (halfProfile q) :=
  (kEvenProfile_integrable hq).const_mul (1 / 2 : ℂ)

private theorem phase_continuous (t : ℝ) : Continuous (phase t) := by
  unfold phase
  fun_prop

private theorem phase_norm (t u : ℝ) : ‖phase t u‖ = 1 := by
  simpa only [phase] using Complex.norm_exp_ofReal_mul_I (2 * t * u)

private theorem halfProfile_mul_phase_integrable {q : ℝ} (hq : 0 < q)
    (t : ℝ) :
    Integrable (fun u : ℝ => halfProfile q u * phase t u) := by
  have hb : ∀ᵐ u : ℝ ∂volume, ‖phase t u‖ ≤ 1 :=
    Filter.Eventually.of_forall (fun u => le_of_eq (phase_norm t u))
  have hi := (halfProfile_integrable hq).smul_bdd 1
    (phase_continuous t).aestronglyMeasurable hb
  simpa only [smul_eq_mul, mul_comm] using hi

private theorem phase_neg (t u : ℝ) :
    phase (-t) u = star (phase t u) := by
  unfold phase
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp only [Complex.conj_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

private theorem phase_add (s t u : ℝ) :
    phase (s + t) u = phase s u * phase t u := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem phase_neg_sub (s t u : ℝ) :
    phase (-(s - t)) u = star (phase s u) * phase t u := by
  calc
    phase (-(s - t)) u = phase (-s + t) u := by congr 1; ring
    _ = phase (-s) u * phase t u := phase_add (-s) t u
    _ = star (phase s u) * phase t u := by rw [phase_neg]

/-- Fourier bridge in full-line exponential form, with its actual half
normalization and `t/π` scale. -/
private theorem imaginaryOrderK_eq_integral_phase (q t : ℝ) (hq : 0 < q) :
    (imaginaryOrderK t q : ℂ) =
      ∫ u : ℝ, halfProfile q u * phase (-t) u := by
  have hangle (u : ℝ) : -2 * π * u * (t / π) = 2 * (-t) * u := by
    field_simp [Real.pi_ne_zero]
    ring
  calc
    (imaginaryOrderK t q : ℂ) =
        (1 / 2 : ℂ) * 𝓕 (kEvenProfile q) (t / π) :=
      imaginaryOrderK_eq_half_fourier t q hq
    _ = (1 / 2 : ℂ) *
        ∫ u : ℝ, Complex.exp (((-2 * π * u * (t / π) : ℝ) : ℂ) *
          Complex.I) * kEvenProfile q u := by
      rw [Real.fourier_real_eq_integral_exp_smul]
      simp only [smul_eq_mul]
    _ = ∫ u : ℝ, (1 / 2 : ℂ) *
        (Complex.exp (((-2 * π * u * (t / π) : ℝ) : ℂ) *
          Complex.I) * kEvenProfile q u) := by
      rw [integral_const_mul]
    _ = ∫ u : ℝ, halfProfile q u * phase (-t) u := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro u
      simp only [halfProfile, phase, hangle]
      ring

/-- The complex Gram form for arbitrary finite frequencies and coefficients. -/
def kGram {n : ℕ} (q : ℝ) (t : Fin n → ℝ) (c : Fin n → ℂ) : ℂ :=
  ∑ i : Fin n, ∑ j : Fin n,
    star (c i) * c j * (imaginaryOrderK (t i - t j) q : ℂ)

def exponentialPolynomial {n : ℕ} (t : Fin n → ℝ)
    (c : Fin n → ℂ) (u : ℝ) : ℂ :=
  ∑ j : Fin n, c j * phase (t j) u

def realEnergy {n : ℕ} (q : ℝ) (t : Fin n → ℝ)
    (c : Fin n → ℂ) (u : ℝ) : ℝ :=
  Real.exp (-q * Real.cosh u) / 2 *
    Complex.normSq (exponentialPolynomial t c u)

private theorem halfProfile_eq_real (q u : ℝ) :
    halfProfile q u = ((Real.exp (-q * Real.cosh u) / 2 : ℝ) : ℂ) := by
  simp only [halfProfile, kEvenProfile, evenLaplaceProfile]
  push_cast
  ring

private theorem gram_integrand_eq_energy {n : ℕ} (q : ℝ)
    (t : Fin n → ℝ) (c : Fin n → ℂ) (u : ℝ) :
    (∑ i : Fin n, ∑ j : Fin n,
      star (c i) * c j *
        (halfProfile q u * phase (-(t i - t j)) u)) =
      (realEnergy q t c u : ℂ) := by
  have hsum :
      (∑ i : Fin n, ∑ j : Fin n,
        star (c i) * c j *
          (halfProfile q u * phase (-(t i - t j)) u)) =
        halfProfile q u *
          ((∑ i : Fin n, star (c i * phase (t i) u)) *
            (∑ j : Fin n, c j * phase (t j) u)) := by
    calc
      (∑ i : Fin n, ∑ j : Fin n,
          star (c i) * c j *
            (halfProfile q u * phase (-(t i - t j)) u)) =
        ∑ i : Fin n, ∑ j : Fin n, halfProfile q u *
          (star (c i * phase (t i) u) *
            (c j * phase (t j) u)) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [phase_neg_sub]
        simp only [star_mul]
        ring
      _ = halfProfile q u *
          (∑ i : Fin n, ∑ j : Fin n,
            star (c i * phase (t i) u) *
              (c j * phase (t j) u)) := by
        simp_rw [Finset.mul_sum]
      _ = halfProfile q u *
          ((∑ i : Fin n, star (c i * phase (t i) u)) *
            (∑ j : Fin n, c j * phase (t j) u)) := by
        rw [Fintype.sum_mul_sum]
  rw [hsum, halfProfile_eq_real]
  simp only [realEnergy, exponentialPolynomial, Complex.ofReal_mul]
  rw [Complex.normSq_eq_conj_mul_self]
  simp only [← star_sum, Complex.star_def]
  ring

private theorem gram_term_integrable {n : ℕ} {q : ℝ} (hq : 0 < q)
    (t : Fin n → ℝ) (c : Fin n → ℂ) (i j : Fin n) :
    Integrable (fun u : ℝ => star (c i) * c j *
      (halfProfile q u * phase (-(t i - t j)) u)) := by
  have h := halfProfile_mul_phase_integrable hq (-(t i - t j))
  simpa only [mul_assoc] using h.const_mul (star (c i) * c j)

/-- Exact Bochner-style Gram representation for the defined K integral.
The right side is an actual nonnegative real integral. -/
theorem kGram_eq_integral_energy {n : ℕ} (q : ℝ) (hq : 0 < q)
    (t : Fin n → ℝ) (c : Fin n → ℂ) :
    kGram q t c = ((∫ u : ℝ, realEnergy q t c u) : ℂ) := by
  let T : Fin n → Fin n → ℝ → ℂ := fun i j u =>
    star (c i) * c j *
      (halfProfile q u * phase (-(t i - t j)) u)
  have hT (i j : Fin n) : Integrable (T i j) :=
    gram_term_integrable hq t c i j
  have hInner (i : Fin n) : Integrable (fun u : ℝ => ∑ j : Fin n, T i j u) :=
    integrable_finsetSum Finset.univ (fun j _ => hT i j)
  have hEntry (i j : Fin n) :
      star (c i) * c j * (imaginaryOrderK (t i - t j) q : ℂ) =
        ∫ u : ℝ, T i j u := by
    rw [imaginaryOrderK_eq_integral_phase q (t i - t j) hq]
    calc
      star (c i) * c j *
          (∫ u : ℝ, halfProfile q u * phase (-(t i - t j)) u) =
          (star (c i) * c j) *
            (∫ u : ℝ, halfProfile q u * phase (-(t i - t j)) u) := by ring
      _ = ∫ u : ℝ, (star (c i) * c j) *
          (halfProfile q u * phase (-(t i - t j)) u) := by
        rw [integral_const_mul]
      _ = ∫ u : ℝ, T i j u := rfl
  calc
    kGram q t c =
        ∑ i : Fin n, ∑ j : Fin n, ∫ u : ℝ, T i j u := by
      simp only [kGram, hEntry]
    _ = ∑ i : Fin n, ∫ u : ℝ, ∑ j : Fin n, T i j u := by
      apply Finset.sum_congr rfl
      intro i _
      exact (integral_finsetSum Finset.univ
        (fun j _ => hT i j)).symm
    _ = ∫ u : ℝ, ∑ i : Fin n, ∑ j : Fin n, T i j u := by
      exact (integral_finsetSum Finset.univ
        (fun i _ => hInner i)).symm
    _ = ((∫ u : ℝ, realEnergy q t c u) : ℂ) := by
      have hpoint (u : ℝ) :
          (∑ i : Fin n, ∑ j : Fin n, T i j u) =
            (realEnergy q t c u : ℂ) :=
        gram_integrand_eq_energy q t c u
      simp_rw [hpoint]
      rw [integral_ofReal]

/-- Integrability of the actual nonnegative Gram density. -/
theorem realEnergy_integrable {n : ℕ} (q : ℝ) (hq : 0 < q)
    (t : Fin n → ℝ) (c : Fin n → ℂ) :
    Integrable (realEnergy q t c) := by
  have hcomplex : Integrable (fun u : ℝ => (realEnergy q t c u : ℂ)) := by
    have hterms (i : Fin n) :
        Integrable (fun u : ℝ => ∑ j : Fin n,
          star (c i) * c j *
            (halfProfile q u * phase (-(t i - t j)) u)) :=
      integrable_finsetSum Finset.univ
        (fun j _ => gram_term_integrable hq t c i j)
    have hsum : Integrable (fun u : ℝ => ∑ i : Fin n, ∑ j : Fin n,
        star (c i) * c j *
          (halfProfile q u * phase (-(t i - t j)) u)) :=
      integrable_finsetSum Finset.univ (fun i _ => hterms i)
    exact hsum.congr (Filter.Eventually.of_forall
      (fun u => gram_integrand_eq_energy q t c u))
  simpa only [Complex.ofReal_re] using hcomplex.re

/-- The Gram form is real and nonnegative for every finite frequency list,
including repeated frequencies and zero coefficients. -/
theorem imaginaryOrderK_positive_definite {n : ℕ} (q : ℝ) (hq : 0 < q)
    (t : Fin n → ℝ) (c : Fin n → ℂ) :
    (kGram q t c).im = 0 ∧ 0 ≤ (kGram q t c).re := by
  rw [kGram_eq_integral_energy q hq t c]
  constructor
  · simp
  · simp only [Complex.ofReal_re]
    apply integral_nonneg
    intro u
    exact mul_nonneg (by positivity) (Complex.normSq_nonneg _)

end
end ImbalancedChen.Part3.KPositiveDefiniteSourceOnly
