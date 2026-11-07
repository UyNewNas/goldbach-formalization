import ImbalancedChen.Part3ActualCriticalPrimeEulerSeries
import ImbalancedChen.Part3EisensteinAmplitudeMultiplicativity

/-! Actual two-prime exponent-lattice Euler series. Native coprime
amplitude multiplicativity identifies every composite coefficient, and
the proved local norm sums pay the genuine double-series rearrangement.
No double summability or Euler factorization is a premise.
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT. -/

noncomputable section
open Complex
open scoped BigOperators
open ImbalancedChen.Part3.NormalizedEisensteinPrimeAmplitude20261026b
open ImbalancedChen.Part3.EisensteinAmplitudeMultiplicativity20261026b
open ImbalancedChen.Part3.ActualCriticalPrimeEulerSeries20261026b

namespace ImbalancedChen.Part3.ActualTwoPrimeEulerSeries20261026b

def twoPrimeEulerTerm (p q : ℕ) (t : ℝ) (X Y : ℂ) (e : ℕ × ℕ) : ℂ :=
  normalizedDivisorAmplitude (p ^ e.1 * q ^ e.2) (1 / 2 + (t : ℂ) * Complex.I) *
    X ^ e.1 * Y ^ e.2

theorem twoPrimeEulerTerm_eq_product {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (t : ℝ) (X Y : ℂ) (e : ℕ × ℕ) :
    twoPrimeEulerTerm p q t X Y e =
      (normalizedDivisorAmplitude (p ^ e.1) (1 / 2 + (t : ℂ) * Complex.I) * X ^ e.1) *
        (normalizedDivisorAmplitude (q ^ e.2) (1 / 2 + (t : ℂ) * Complex.I) * Y ^ e.2) := by
  have hcop : (p ^ e.1).Coprime (q ^ e.2) :=
    (((Nat.coprime_primes hp hq).mpr hpq).pow_left e.1).pow_right e.2
  unfold twoPrimeEulerTerm
  rw [normalizedAmplitude_mul_of_coprime hcop]
  ring

/-- Genuine absolute convergence over every composite exponent pair. -/
theorem twoPrimeEuler_norm_summable {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (t : ℝ) {X Y : ℂ} (hX : ‖X‖ < 1) (hY : ‖Y‖ < 1) :
    Summable (fun e : ℕ × ℕ => ‖twoPrimeEulerTerm p q t X Y e‖) := by
  have h := (actualCriticalLocalEuler_norm_summable hp t hX).mul_norm
    (actualCriticalLocalEuler_norm_summable hq t hY)
  exact h.congr (fun e => congrArg norm (twoPrimeEulerTerm_eq_product hp hq hpq t X Y e).symm)

/-- Actual double Euler coefficient series equals the finite product of
the two genuine convergent local factors. Each denominator is nonzero
by the local theorem, including at the central spectral parameter. -/
theorem twoPrimeEuler_eq_product {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (t : ℝ) {X Y : ℂ} (hX : ‖X‖ < 1) (hY : ‖Y‖ < 1) :
    (∑' e : ℕ × ℕ, twoPrimeEulerTerm p q t X Y e) =
      (1 - criticalPrimeScalar p t * X + X ^ 2)⁻¹ *
        (1 - criticalPrimeScalar q t * Y + Y ^ 2)⁻¹ := by
  have hf := actualCriticalLocalEuler_norm_summable hp t hX
  have hg := actualCriticalLocalEuler_norm_summable hq t hY
  calc
    _ = ∑' e : ℕ × ℕ,
        (normalizedDivisorAmplitude (p ^ e.1) (1 / 2 + (t : ℂ) * Complex.I) * X ^ e.1) *
          (normalizedDivisorAmplitude (q ^ e.2) (1 / 2 + (t : ℂ) * Complex.I) * Y ^ e.2) :=
      tsum_congr (twoPrimeEulerTerm_eq_product hp hq hpq t X Y)
    _ = actualCriticalLocalEulerSeries p t X * actualCriticalLocalEulerSeries q t Y :=
      (tsum_mul_tsum_of_summable_norm hf hg).symm
    _ = _ := by rw [(actualCriticalLocalEuler_eq_inverse hp t hX).2,
      (actualCriticalLocalEuler_eq_inverse hq t hY).2]

end ImbalancedChen.Part3.ActualTwoPrimeEulerSeries20261026b
