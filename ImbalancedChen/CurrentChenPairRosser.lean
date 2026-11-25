import ImbalancedChen.CurrentChenInitialRosser
import ImbalancedChen.CurrentChenPairLevelGeometry

/-!
# The same actual Rosser lower coefficient on literal quotient sources

The finite lower sieve is proved on the actual injective quotient source.
Fubini keeps the physical modulus `b * d`. On its genuine divisor support,
the rough-multiplier gate makes the main term exactly the original Rosser
density divided by `phi b`. Every prime-centre correction is retained.

These are finite theorems, with no distribution or density estimate as a
hypothesis. The active row support at the rounded quotient level has its
full physical modulus at most Q. No positive lower factor is assigned to
the full sixth rectangle.
-/

namespace ImbalancedChen

noncomputable section

open Filter
open scoped BigOperators
open Classical
open MathlibNt.SieveTheory.BombieriVinogradov (trueLogarithmicIntegral)

/-- Exact finite Fubini on the literal quotient source. -/
theorem currentChen_quotient_sum_supportedDivisorSum
    (N b : ℕ) (S : Finset ℕ) (beta : ℕ → ℝ) :
    (∑ q ∈ chenQuotientPrimeSource N b, supportedDivisorSum S beta q) =
      ∑ d ∈ S, beta d *
        (chenPrimeAPCount N N (b * d) - chenCentrePrimeAPCount N N (b * d)) := by
  simp only [supportedDivisorSum, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  calc
    (∑ q ∈ chenQuotientPrimeSource N b, if d ∣ q then beta d else 0) =
        (((chenQuotientPrimeSource N b).filter (fun q => d ∣ q)).card : ℝ) *
          beta d := by
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ = _ := by
      rw [chenQuotientPrimeSource_divisibility_fibre_card]
      ring

/-- The pointwise provider lower sieve applies to these actual receivers,
including the quotient one and the complete target-coprimality mask. -/
theorem currentChen_quotient_actualRosser_lower
    (N b cap : ℕ) (z L : ℝ) (hzcap : z ≤ (cap : ℝ))
    (hL : 1 < L) (hzL : z ≤ L) :
    (∑ d ∈ actualSmallRosserSupport N cap z,
      actualSmallRosserMinus N cap z L d *
        (chenPrimeAPCount N N (b * d) - chenCentrePrimeAPCount N N (b * d))) ≤
      ((chenSiftedQuotientPrimeSource N b z).card : ℝ) := by
  rw [← currentChen_quotient_sum_supportedDivisorSum]
  calc
    _ ≤ ∑ q ∈ chenQuotientPrimeSource N b,
        if Nat.Coprime q (sieveProduct N (Nat.ceil z)) then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro q _
      have h := (actualSmallRosser_sandwich_nat N cap z L hL hzL q).1
      rw [currentChen_actualSmallPrimeProduct_eq_sieveProduct N cap z hzcap] at h
      simpa only [Nat.coprime_comm] using h
    _ = _ := by
      rw [← Finset.sum_filter, ← chenSiftedQuotientPrimeSource_eq_coprime_filter]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- Exact main term and errors at the full physical prime-AP modulus.
The condition on b is proved by the actual fifth/sixth selector gates. -/
theorem currentChen_quotient_actualRosser_main_and_errors
    (N b cap : ℕ) (z L : ℝ) (hzcap : z ≤ (cap : ℝ))
    (hb : Nat.Coprime b (sieveProduct N (Nat.ceil z))) :
    (∑ d ∈ actualSmallRosserSupport N cap z,
      actualSmallRosserMinus N cap z L d *
        (chenPrimeAPCount N N (b * d) - chenCentrePrimeAPCount N N (b * d))) =
      trueLogarithmicIntegral N / (Nat.totient b : ℝ) *
          actualSmallRosserMinusDensity N cap z L +
        (∑ d ∈ actualSmallRosserSupport N cap z,
          actualSmallRosserMinus N cap z L d *
            chenQuotientPrimeAPError N (trueLogarithmicIntegral N) (b * d)) -
        ∑ d ∈ actualSmallRosserSupport N cap z,
          actualSmallRosserMinus N cap z L d * chenCentrePrimeAPCount N N (b * d) := by
  simp only [actualSmallRosserMinusDensity, reciprocalTotientDensity,
    Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  have hdP : d ∣ sieveProduct N (Nat.ceil z) := by
    have hdM := (Nat.mem_divisors.mp hd).1
    rwa [currentChen_actualSmallPrimeProduct_eq_sieveProduct N cap z hzcap] at hdM
  have hcop := chenQuotient_allowed_coprime hb hdP
  unfold chenQuotientPrimeAPError
  rw [Nat.totient_mul hcop, Nat.cast_mul]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- A true quotient-count bound carrying the genuine Rosser density and
all signed actual errors; no analytic supplier is a premise. -/
theorem currentChen_quotient_actualRosser_density_lower
    (N b cap : ℕ) (z L : ℝ) (hzcap : z ≤ (cap : ℝ))
    (hb : Nat.Coprime b (sieveProduct N (Nat.ceil z)))
    (hL : 1 < L) (hzL : z ≤ L) :
    trueLogarithmicIntegral N / (Nat.totient b : ℝ) *
        actualSmallRosserMinusDensity N cap z L +
      (∑ d ∈ actualSmallRosserSupport N cap z,
        actualSmallRosserMinus N cap z L d *
          chenQuotientPrimeAPError N (trueLogarithmicIntegral N) (b * d)) -
      (∑ d ∈ actualSmallRosserSupport N cap z,
        actualSmallRosserMinus N cap z L d * chenCentrePrimeAPCount N N (b * d)) ≤
      ((chenSiftedQuotientPrimeSource N b z).card : ℝ) := by
  rw [← currentChen_quotient_actualRosser_main_and_errors N b cap z L hzcap hb]
  exact currentChen_quotient_actualRosser_lower N b cap z L hzcap hL hzL

/-- Nonzero coefficients only: the complete displayed divisor support
need not satisfy the physical level cap. -/
def currentChenQuotientRosserActive (N b cap Q : ℕ) (z : ℝ) : Finset ℕ :=
  (actualSmallRosserSupport N cap z).filter
    (fun d => actualSmallRosserMinus N cap z (chenQuotientRowLevel Q b : ℝ) d ≠ 0)

/-- Every active row has the literal full physical modulus b*d <= Q. -/
theorem currentChenQuotientRosserActive_physical_cap
    {N b cap Q d : ℕ} {z : ℝ} (hb : 0 < b)
    (hd : d ∈ currentChenQuotientRosserActive N b cap Q z) : b * d ≤ Q := by
  have hactive := (actualSmallRosserMinus_active (Finset.mem_filter.mp hd).2).2.1
  have hlt : d < chenQuotientRowLevel Q b := by exact_mod_cast hactive
  exact (lt_chenQuotientRowLevel_iff hb).mp hlt

/-- Active supports are genuine divisors of the same strict sieve product. -/
theorem currentChenQuotientRosserActive_divisor
    {N b cap Q d : ℕ} {z : ℝ} (hzcap : z ≤ (cap : ℝ))
    (hd : d ∈ currentChenQuotientRosserActive N b cap Q z) :
    d ∈ (sieveProduct N (Nat.ceil z)).divisors := by
  have hds := (Finset.mem_filter.mp hd).1
  change d ∈ (actualSmallPrimeProduct N cap z).divisors at hds
  rwa [currentChen_actualSmallPrimeProduct_eq_sieveProduct N cap z hzcap] at hds

/-- Removing inactive displayed divisors is an exact equality. -/
theorem currentChen_quotientRosser_sum_eq_active
    (N b cap Q : ℕ) (z : ℝ) (f : ℕ → ℝ) :
    (∑ d ∈ actualSmallRosserSupport N cap z,
      actualSmallRosserMinus N cap z (chenQuotientRowLevel Q b : ℝ) d * f d) =
      ∑ d ∈ currentChenQuotientRosserActive N b cap Q z,
        actualSmallRosserMinus N cap z (chenQuotientRowLevel Q b : ℝ) d * f d := by
  simp only [currentChenQuotientRosserActive, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d _
  by_cases h : actualSmallRosserMinus N cap z (chenQuotientRowLevel Q b : ℝ) d = 0
  · simp only [h, ne_eq, not_true_eq_false, if_false, zero_mul]
  · simp only [h, ne_eq, not_false_eq_true, if_true]

end

end ImbalancedChen
