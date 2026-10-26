import ImbalancedChen.Part3RoughSlotDirichletSeries
import ImbalancedChen.Part3PrimeMellinProfileVariation

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual complex Mellin modulation exp(i*t*log(n/U)) shifts the genuine
rough-slot Dirichlet exponent to s-i*t and contributes exp(-i*t*log U).
The real part and absolute-convergence half-plane are unchanged. The two
finite Euler corrections keep the exact p<=z endpoint and all character
zero factors. This is a series identity, not an SW or zero-free estimate.
-/

namespace ImbalancedChen.Part3.RoughSlotMellinSeries20261026b
noncomputable section
open Classical Complex
open scoped BigOperators
open RoughSlotCharacterLift20261026b RoughSlotDirichletSeries20261026b
open PrimeMellinProfileVariation20261026b

def shiftedExponent (s : ℂ) (t : ℝ) : ℂ := s-Complex.I*(t : ℂ)

theorem shiftedExponent_re (s : ℂ) (t : ℝ) : (shiftedExponent s t).re = s.re := by
  simp [shiftedExponent]

theorem phase_scale {U x : ℝ} (hU : 0 < U) (hx : 0 < x) (t : ℝ) :
    phase t (x/U) = phase (-t) U*phase t x := by
  unfold phase
  rw [Real.log_div hx.ne' hU.ne',Complex.ofReal_sub,← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem phase_eq_cpow {x : ℝ} (hx : 0 < x) (t : ℝ) :
    phase t x = (x : ℂ)^(Complex.I*(t : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    ← Complex.ofReal_log hx.le]
  unfold phase
  congr 1
  ring

/-- Exact summand identity, including the intentionally zero LSeries
term at n=0. No convergence or analytic estimate is a premise. -/
theorem mellin_term_shift (f : ℕ → ℂ) {U : ℝ} (hU : 0 < U)
    (s : ℂ) (t : ℝ) (n : ℕ) :
    LSeries.term (fun n => phase t ((n : ℝ)/U)*f n) s n =
      phase (-t) U*LSeries.term f (shiftedExponent s t) n := by
  by_cases hn : n = 0
  · simp only [hn,LSeries.term_zero,mul_zero]
  · have hnR : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    rw [LSeries.term_of_ne_zero hn,LSeries.term_of_ne_zero hn,
      phase_scale hU hnR,phase_eq_cpow hnR]
    simp only [Complex.ofReal_natCast,shiftedExponent,Complex.cpow_sub _ _ hnC,
      div_eq_mul_inv,mul_inv_rev,inv_inv]
    ring

theorem mellin_LSeries_shift (f : ℕ → ℂ) {U : ℝ} (hU : 0 < U)
    (s : ℂ) (t : ℝ) :
    LSeries (fun n => phase t ((n : ℝ)/U)*f n) s =
      phase (-t) U*LSeries f (shiftedExponent s t) := by
  unfold LSeries
  simp_rw [mellin_term_shift f hU s t]
  rw [tsum_mul_left]

def roughOneMellin {q : ℕ} (chi : DirichletCharacter ℂ q)
    (z t U : ℝ) (n : ℕ) : ℂ :=
  phase t ((n : ℝ)/U)*(chi n*roughOneSlot z n)

def roughMoebiusMellin {q : ℕ} (chi : DirichletCharacter ℂ q)
    (z t U : ℝ) (n : ℕ) : ℂ :=
  phase t ((n : ℝ)/U)*(chi n*roughMoebiusSlot z n)

/-- Complex Mellin twisting leaves the actual absolute-convergence
half-plane unchanged. This follows from the unit phase coefficient norm. -/
theorem roughMellin_LSeriesSummable {q : ℕ} (chi : DirichletCharacter ℂ q)
    (z t U : ℝ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (roughOneMellin chi z t U) s ∧
      LSeriesSummable (roughMoebiusMellin chi z t U) s := by
  constructor
  · apply LSeriesSummable_of_bounded_of_one_lt_re (m := 1) _ hs
    intro n hn
    simp only [roughOneMellin,norm_mul,phase_norm,one_mul]
    exact (mul_le_mul (chi.norm_le_one n) (roughOneSlot_norm_le z n)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  · apply LSeriesSummable_of_bounded_of_one_lt_re (m := 1) _ hs
    intro n hn
    simp only [roughMoebiusMellin,norm_mul,phase_norm,one_mul]
    exact (mul_le_mul (chi.norm_le_one n) (roughMoebiusSlot_norm_le z n)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

/-- Exact actual complex-Mellin rough-one and rough-Mobius series. The
character may be principal, and finite correction primes dividing its
original level have factor one by the preceding source. -/
theorem actual_rough_Mellin_Dirichlet_series {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {z U : ℝ} (hz : 0 ≤ z) (hU : 0 < U)
    (t : ℝ) {s : ℂ} (hs : 1 < s.re) :
    (∑' n : ℕ, roughOneMellin chi z t U n/(n : ℂ)^s) =
        phase (-t) U*(chi.LFunction (shiftedExponent s t)*
          finiteCorrection chi z (shiftedExponent s t)) ∧
      (∑' n : ℕ, roughMoebiusMellin chi z t U n/(n : ℂ)^s) =
        phase (-t) U*((chi.LFunction (shiftedExponent s t))⁻¹*
          (∏ p ∈ smallPrimes z,
            (1-chi p*(p : ℂ)^(-(shiftedExponent s t)))⁻¹)) := by
  have hshift : 1 < (shiftedExponent s t).re := by
    simpa only [shiftedExponent_re] using hs
  have hone := mellin_LSeries_shift (fun n : ℕ => chi n*roughOneSlot z n) hU s t
  rw [roughOne_LSeries chi hz hshift] at hone
  have hmu := mellin_LSeries_shift (fun n : ℕ => chi n*roughMoebiusSlot z n) hU s t
  rw [roughMoebius_LSeries chi hz hshift] at hmu
  constructor
  · simpa only [roughOneMellin,LSeries,
      LSeries.term_of_ne_zero' (Complex.ne_zero_of_one_lt_re hs)] using hone
  · simpa only [roughMoebiusMellin,LSeries,
      LSeries.term_of_ne_zero' (Complex.ne_zero_of_one_lt_re hs)] using hmu

end
end ImbalancedChen.Part3.RoughSlotMellinSeries20261026b
