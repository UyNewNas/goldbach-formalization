import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Tactic

/-!
SOURCE ONLY, 2026-10-25. UNCOMPILED; NOT ROOT ACCEPTED.

The actual Euler-totient Dirichlet series, independently of the held coordinate
Eisenstein source chain. The arithmetic input is Nat.sum_totient. We derive the
literal coefficient convolution phi convolution 1 = n, establish convergence
from phi(n) <= n, and apply the pinned absolutely convergent L-series product
theorem. Its implementation supplies the double-tsum and multiplicative-fiber
exchange; the target Dirichlet identity is not an assumption.

For real s > 1, the final theorem identifies the real sum of phi(c)/c^(2s)
with zeta(2s-1)/zeta(2s), after embedding the real sum into the complex numbers.
The c=0 summand is zero, so this is the usual series over c >= 1.
-/

namespace ImbalancedChen.Part3.ActualTotientDirichletSeries

noncomputable section

open Complex
open scoped LSeries.notation

/-- Literal complex Euler-totient coefficients. -/
def totientCoeff (n : ℕ) : ℂ := n.totient

@[simp] theorem totientCoeff_zero : totientCoeff 0 = 0 := by simp [totientCoeff]

/-- Actual coefficient convolution, proved from the finite divisor identity. -/
theorem totientCoeff_convolution_one :
    totientCoeff ⍟ (1 : ℕ → ℂ) = (fun n : ℕ => (n : ℂ)) := by
  funext n
  rw [LSeries.convolution_def]
  change (∑ p ∈ n.divisorsAntidiagonal, (p.1.totient : ℂ) * 1) = (n : ℂ)
  simp only [mul_one]
  rw [Nat.sum_divisorsAntidiagonal (fun a _ => (a.totient : ℂ))]
  exact_mod_cast Nat.sum_totient n

/-- Absolute convergence of the complex totient L-series for re z > 2. -/
theorem totientCoeff_LSeriesSummable {z : ℂ} (hz : 2 < z.re) :
    LSeriesSummable totientCoeff z := by
  apply LSeriesSummable_of_le_const_mul_rpow (x := 2) hz
  refine ⟨1, ?_⟩
  intro n hn
  have hphi : (n.totient : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.totient_le n
  simpa [totientCoeff, show (2 : ℝ) - 1 = 1 by norm_num] using hphi

/-- Absolute convergence of the actual double series used in the
multiplicative convolution/fiber exchange. -/
theorem totient_product_terms_abs_summable {z : ℂ} (hz : 2 < z.re) :
    Summable (fun p : ℕ × ℕ =>
      ‖LSeries.term totientCoeff z p.1 * LSeries.term (1 : ℕ → ℂ) z p.2‖) := by
  have hone : LSeriesSummable (1 : ℕ → ℂ) z :=
    LSeriesSummable_one_iff.mpr (by linarith)
  exact (summable_mul_of_summable_norm (totientCoeff_LSeriesSummable hz).norm
    hone.norm).norm

/-- Multiplying the coefficients by n shifts the constant-one L-series by one. -/
theorem LSeries_natCoeff_eq_riemannZeta {z : ℂ} (hz : 2 < z.re) :
    LSeries (fun n : ℕ => (n : ℂ)) z = riemannZeta (z - 1) := by
  have hz1 : 1 < (z - 1).re := by simpa using (show 1 < z.re - 1 by linarith)
  rw [← LSeries_one_eq_riemannZeta hz1]
  unfold LSeries
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · simp [hn]
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    simp only [Pi.one_apply]
    have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    have hpow : (n : ℂ) ^ z ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hnC)
    rw [Complex.cpow_sub z 1 hnC, Complex.cpow_one]
    field_simp [hnC, hpow] <;> ring

/-- The actual absolutely convergent totient series times zeta equals the
shifted zeta function. The convolution exchange is the pinned Mathlib theorem. -/
theorem totient_LSeries_mul_zeta {z : ℂ} (hz : 2 < z.re) :
    LSeries totientCoeff z * riemannZeta z = riemannZeta (z - 1) := by
  have hz1 : 1 < z.re := by linarith
  have hphi := totientCoeff_LSeriesSummable hz
  have hone : LSeriesSummable (1 : ℕ → ℂ) z := LSeriesSummable_one_iff.mpr hz1
  calc
    _ = LSeries totientCoeff z * LSeries (1 : ℕ → ℂ) z := by
      rw [LSeries_one_eq_riemannZeta hz1]
    _ = LSeries (totientCoeff ⍟ (1 : ℕ → ℂ)) z := (LSeries_convolution' hphi hone).symm
    _ = LSeries (fun n : ℕ => (n : ℂ)) z := by rw [totientCoeff_convolution_one]
    _ = riemannZeta (z - 1) := LSeries_natCoeff_eq_riemannZeta hz

/-- Genuine totient Dirichlet quotient identity on its half plane of absolute
convergence, with zeta nonvanishing supplied by the pinned theorem. -/
theorem totient_LSeries_eq_zeta_quotient {z : ℂ} (hz : 2 < z.re) :
    LSeries totientCoeff z = riemannZeta (z - 1) / riemannZeta z := by
  have hn : riemannZeta z ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by linarith)
  exact (eq_div_iff hn).2 (totient_LSeries_mul_zeta hz)

/-- Literal real summand. The term at zero is zero, so the natural-indexed
sum below is exactly the ordinary positive-integer Dirichlet series. -/
def totientTerm (s : ℝ) (n : ℕ) : ℝ := (n.totient : ℝ) / (n : ℝ) ^ (2 * s)

@[simp] theorem totientTerm_zero (s : ℝ) : totientTerm s 0 = 0 := by
  simp [totientTerm]

theorem totientTerm_nonneg (s : ℝ) (n : ℕ) : 0 ≤ totientTerm s n := by
  unfold totientTerm
  positivity

/-- The real summand is dominated by n^(1-2s), using the actual inequality
phi(n) <= n. No Dirichlet-series identity is used for convergence. -/
theorem totientTerm_le_rpow (s : ℝ) (n : ℕ) :
    totientTerm s n ≤ (n : ℝ) ^ (1 - 2 * s) := by
  by_cases hn : n = 0
  · subst n
    rw [totientTerm_zero]
    positivity
  · have hnR : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hphi : (n.totient : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.totient_le n
    calc
      _ ≤ (n : ℝ) / (n : ℝ) ^ (2 * s) :=
        div_le_div_of_nonneg_right hphi (Real.rpow_nonneg hnR.le _)
      _ = (n : ℝ) ^ (1 - 2 * s) := by
        rw [Real.rpow_sub hnR 1 (2 * s), Real.rpow_one]

/-- Absolute convergence of the actual real totient series for s > 1. -/
theorem totientTerm_summable (s : ℝ) (hs : 1 < s) : Summable (totientTerm s) := by
  have hmaj : Summable (fun n : ℕ => (n : ℝ) ^ (1 - 2 * s)) :=
    summable_nat_rpow.mpr (by linarith)
  exact hmaj.of_nonneg_of_le (totientTerm_nonneg s) (totientTerm_le_rpow s)

theorem abs_totientTerm_summable (s : ℝ) (hs : 1 < s) :
    Summable (fun n : ℕ => |totientTerm s n|) := by
  simpa only [Real.norm_eq_abs] using (totientTerm_summable s hs).norm

/-- Exact bridge between the real series and the complex L-series definition. -/
theorem totient_LSeries_ofReal (u : ℝ) :
    LSeries totientCoeff (u : ℂ) =
      ((∑' n : ℕ, (n.totient : ℝ) / (n : ℝ) ^ u) : ℂ) := by
  rw [LSeries_def₀ totientCoeff_zero, Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  simp only [totientCoeff, Complex.ofReal_div, Complex.ofReal_natCast,
    Complex.ofReal_cpow (Nat.cast_nonneg n) u]

/-- The classical totient series identity at the real Eisenstein exponent.
Both zeta factors are the actual pinned Riemann zeta function. -/
theorem actual_totient_series_eq_zeta_quotient (s : ℝ) (hs : 1 < s) :
    ((∑' n : ℕ, totientTerm s n) : ℂ) =
      riemannZeta ((2 * s - 1 : ℝ) : ℂ) / riemannZeta ((2 * s : ℝ) : ℂ) := by
  have hz : 2 < ((2 * s : ℝ) : ℂ).re := by simpa using (show 2 < 2 * s by linarith)
  have h := totient_LSeries_eq_zeta_quotient hz
  rw [totient_LSeries_ofReal] at h
  simpa only [totientTerm, Complex.ofReal_sub, Complex.ofReal_one] using h

/-- Real-valued spelling of the same exact quotient formula. -/
theorem actual_totient_series_eq_zeta_quotient_re (s : ℝ) (hs : 1 < s) :
    (∑' n : ℕ, totientTerm s n) =
      (riemannZeta ((2 * s - 1 : ℝ) : ℂ) / riemannZeta ((2 * s : ℝ) : ℂ)).re := by
  simpa only [Complex.ofReal_re] using
    congrArg Complex.re (actual_totient_series_eq_zeta_quotient s hs)

end

end ImbalancedChen.Part3.ActualTotientDirichletSeries
