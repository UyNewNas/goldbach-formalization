import ImbalancedChen.Part3KPositiveDefinite
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-!
SOURCEONLY / UNCOMPILED, 2026-10-24.

Strict positive definiteness of the actual height-difference kernel
`imaginaryOrderK (t_i - t_j) q` for distinct real heights and q > 0.
This is different from the sum-of-q kernel `K₀(q_i + q_j)`.
The proof uses Dedekind independence of distinct exponential characters,
then full support of Lebesgue measure for strict positivity of the energy.
-/

noncomputable section

namespace ImbalancedChen.Part3.KStrictPositiveDefiniteSourceOnly

open MeasureTheory
open scoped BigOperators
open ImbalancedChen.Part3.ImaginaryOrderKBesselSourceOnly
open ImbalancedChen.Part3.KPositiveDefiniteSourceOnly

/-- The real-frequency character on the multiplicative presentation of `(ℝ,+)`. -/
def phaseCharacter (t : ℝ) : Multiplicative ℝ →* ℂ where
  toFun x := Complex.exp
    (((2 * t * (Multiplicative.toAdd x : ℝ) : ℝ) : ℂ) * Complex.I)
  map_one' := by simp
  map_mul' x y := by
    change Complex.exp
      (((2 * t * ((Multiplicative.toAdd x : ℝ) +
        (Multiplicative.toAdd y : ℝ)) : ℝ) : ℂ) * Complex.I) =
      Complex.exp
        (((2 * t * (Multiplicative.toAdd x : ℝ) : ℝ) : ℂ) * Complex.I) *
      Complex.exp
        (((2 * t * (Multiplicative.toAdd y : ℝ) : ℝ) : ℂ) * Complex.I)
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring

/-- Two frequency characters equal as functions on the full real line
only when their real frequencies agree. The separating point is explicit. -/
theorem phaseCharacter_injective : Function.Injective phaseCharacter := by
  intro s t h
  by_contra hst
  have hdiff : s - t ≠ 0 := sub_ne_zero.mpr hst
  let u : ℝ := Real.pi / (2 * (s - t))
  have hreal : 2 * s * u = Real.pi + 2 * t * u := by
    dsimp [u]
    field_simp [hdiff]
    ring
  have harg :
      (((2 * s * u : ℝ) : ℂ) * Complex.I) =
        ((Real.pi : ℂ) * Complex.I) +
          (((2 * t * u : ℝ) : ℂ) * Complex.I) := by
    calc
      (((2 * s * u : ℝ) : ℂ) * Complex.I) =
          (((Real.pi + 2 * t * u : ℝ) : ℂ) * Complex.I) :=
        congrArg (fun x : ℝ => (x : ℂ) * Complex.I) hreal
      _ = _ := by push_cast; ring
  have hpoint : Complex.exp (((2 * s * u : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((2 * t * u : ℝ) : ℂ) * Complex.I) := by
    simpa only [phaseCharacter, Multiplicative.toAdd_ofAdd] using
      congrArg (fun χ : Multiplicative ℝ →* ℂ =>
        χ (Multiplicative.ofAdd u)) h
  rw [harg, Complex.exp_add, Complex.exp_pi_mul_I] at hpoint
  have hz : Complex.exp (((2 * t * u : ℝ) : ℂ) * Complex.I) = 0 := by
    linear_combination hpoint
  exact (Complex.exp_ne_zero _) hz

/-- Pointwise linear independence of the actual finite exponential
polynomials, proved through Dedekind's theorem for monoid characters. -/
theorem exponentialPolynomial_exists_ne_zero {n : ℕ}
    (t : Fin n → ℝ) (hinj : Function.Injective t)
    (c : Fin n → ℂ) (hc : c ≠ 0) :
    ∃ u : ℝ, exponentialPolynomial t c u ≠ 0 := by
  classical
  have hχ : LinearIndependent ℂ
      (fun i : Fin n =>
        (phaseCharacter (t i) : Multiplicative ℝ → ℂ)) :=
    ((linearIndependent_monoidHom (Multiplicative ℝ) ℂ).comp
      phaseCharacter phaseCharacter_injective).comp t hinj
  by_contra hnone
  have hall : ∀ u : ℝ, exponentialPolynomial t c u = 0 := by
    simpa only [not_exists, not_not] using hnone
  have hsum :
      (∑ i : Fin n,
        c i • (phaseCharacter (t i) : Multiplicative ℝ → ℂ)) = 0 := by
    funext x
    have hx := hall (Multiplicative.toAdd x)
    change (∑ i : Fin n,
      c i * Complex.exp
        (((2 * t i * (Multiplicative.toAdd x : ℝ) : ℝ) : ℂ) * Complex.I)) = 0 at hx
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply, phaseCharacter] using hx
  apply hc
  funext i
  exact (Fintype.linearIndependent_iff.1 hχ) c hsum i

/-- The actual finite height-difference Gram form is strictly positive
for every nonzero complex coefficient vector at distinct real heights. -/
theorem imaginaryOrderK_strictly_positive_definite {n : ℕ}
    (q : ℝ) (hq : 0 < q) (t : Fin n → ℝ)
    (hinj : Function.Injective t) (c : Fin n → ℂ) (hc : c ≠ 0) :
    (kGram q t c).im = 0 ∧ 0 < (kGram q t c).re := by
  obtain ⟨u, hu⟩ := exponentialPolynomial_exists_ne_zero t hinj c hc
  have hcont : Continuous (realEnergy q t c) := by
    unfold realEnergy exponentialPolynomial
    fun_prop
  have hnonneg : 0 ≤ realEnergy q t c := by
    intro x
    exact mul_nonneg (by positivity) (Complex.normSq_nonneg _)
  have hpoint : realEnergy q t c u ≠ 0 := by
    have hp : 0 < realEnergy q t c u := by
      unfold realEnergy
      exact mul_pos (div_pos (Real.exp_pos _) (by norm_num))
        (Complex.normSq_pos.mpr hu)
    exact ne_of_gt hp
  have hpos : 0 < ∫ x : ℝ, realEnergy q t c x :=
    integral_pos_of_integrable_nonneg_nonzero hcont
      (realEnergy_integrable q hq t c) hnonneg hpoint
  rw [kGram_eq_integral_energy q hq t c]
  exact ⟨by simp, by simpa only [Complex.ofReal_re] using hpos⟩

/-- An explicitly stated complex Hermitian Gram inequality, without the
auxiliary `kGram` abbreviation. -/
theorem imaginaryOrderK_difference_gram_pos {n : ℕ}
    (q : ℝ) (hq : 0 < q) (t : Fin n → ℝ)
    (hinj : Function.Injective t) (c : Fin n → ℂ) (hc : c ≠ 0) :
    0 < (∑ i : Fin n, ∑ j : Fin n,
      star (c i) * c j *
        (imaginaryOrderK (t i - t j) q : ℂ)).re :=
  (imaginaryOrderK_strictly_positive_definite q hq t hinj c hc).2

end ImbalancedChen.Part3.KStrictPositiveDefiniteSourceOnly
