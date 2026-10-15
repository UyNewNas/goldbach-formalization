import ImbalancedChen.CurrentChenPairRosser

/-!
# The actual upper Rosser coefficient on literal quotient sources

The finite upper sieve uses the same actual product and the literal strict
row level. Fubini retains the full physical modulus `b*d`, the exact
reciprocal-totient density and every signed prime-AP and centre correction.
Only nonzero coefficients are removed from the displayed divisor support.
No distribution estimate or analytic density bound is assumed.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators
open Classical
open MathlibNt.SieveTheory.BombieriVinogradov (trueLogarithmicIntegral)

/-- The proved upper sieve on the actual quotient receiver carrier. -/
theorem currentChen_quotient_actualRosser_upper
    (N b cap : ℕ) (z L : ℝ) (hzcap : z ≤ (cap : ℝ))
    (hL : 1 < L) (hzL : z ≤ L) :
    ((chenSiftedQuotientPrimeSource N b z).card : ℝ) ≤
      ∑ d ∈ actualSmallRosserSupport N cap z,
        actualSmallRosserPlus N cap z L d *
          (chenPrimeAPCount N N (b * d) - chenCentrePrimeAPCount N N (b * d)) := by
  rw [← currentChen_quotient_sum_supportedDivisorSum]
  calc
    _ = ∑ q ∈ chenQuotientPrimeSource N b,
        if Nat.Coprime q (sieveProduct N (Nat.ceil z)) then (1 : ℝ) else 0 := by
      rw [← Finset.sum_filter, ← chenSiftedQuotientPrimeSource_eq_coprime_filter]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro q _
      have h := (actualSmallRosser_sandwich_nat N cap z L hL hzL q).2
      rw [currentChen_actualSmallPrimeProduct_eq_sieveProduct N cap z hzcap] at h
      simpa only [Nat.coprime_comm] using h

/-- The exact upper-density main term and all signed errors. -/
theorem currentChen_quotient_actualRosser_plus_main_and_errors
    (N b cap : ℕ) (z L : ℝ) (hzcap : z ≤ (cap : ℝ))
    (hb : Nat.Coprime b (sieveProduct N (Nat.ceil z))) :
    (∑ d ∈ actualSmallRosserSupport N cap z,
      actualSmallRosserPlus N cap z L d *
        (chenPrimeAPCount N N (b * d) - chenCentrePrimeAPCount N N (b * d))) =
      trueLogarithmicIntegral N / (Nat.totient b : ℝ) *
          actualSmallRosserPlusDensity N cap z L +
        (∑ d ∈ actualSmallRosserSupport N cap z,
          actualSmallRosserPlus N cap z L d *
            chenQuotientPrimeAPError N (trueLogarithmicIntegral N) (b * d)) -
        ∑ d ∈ actualSmallRosserSupport N cap z,
          actualSmallRosserPlus N cap z L d * chenCentrePrimeAPCount N N (b * d) := by
  simp only [actualSmallRosserPlusDensity, reciprocalTotientDensity,
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

/-- The actual quotient count is bounded above by its same-coefficient
upper-density main term, with every signed error still present. -/
theorem currentChen_quotient_actualRosser_density_upper
    (N b cap : ℕ) (z L : ℝ) (hzcap : z ≤ (cap : ℝ))
    (hb : Nat.Coprime b (sieveProduct N (Nat.ceil z)))
    (hL : 1 < L) (hzL : z ≤ L) :
    ((chenSiftedQuotientPrimeSource N b z).card : ℝ) ≤
      trueLogarithmicIntegral N / (Nat.totient b : ℝ) *
          actualSmallRosserPlusDensity N cap z L +
        (∑ d ∈ actualSmallRosserSupport N cap z,
          actualSmallRosserPlus N cap z L d *
            chenQuotientPrimeAPError N (trueLogarithmicIntegral N) (b * d)) -
        ∑ d ∈ actualSmallRosserSupport N cap z,
          actualSmallRosserPlus N cap z L d * chenCentrePrimeAPCount N N (b * d) := by
  rw [← currentChen_quotient_actualRosser_plus_main_and_errors N b cap z L hzcap hb]
  exact currentChen_quotient_actualRosser_upper N b cap z L hzcap hL hzL

/-- The complete nonzero support of the actual upper coefficient. -/
def currentChenQuotientUpperRosserActive (N b cap Q : ℕ) (z : ℝ) : Finset ℕ :=
  (actualSmallRosserSupport N cap z).filter
    (fun d => actualSmallRosserPlus N cap z (chenQuotientRowLevel Q b : ℝ) d ≠ 0)

/-- A nonzero upper coefficient has full physical modulus at most Q. -/
theorem currentChenQuotientUpperRosserActive_physical_cap
    {N b cap Q d : ℕ} {z : ℝ} (hb : 0 < b)
    (hd : d ∈ currentChenQuotientUpperRosserActive N b cap Q z) : b * d ≤ Q := by
  have hactive := (actualSmallRosserPlus_active (Finset.mem_filter.mp hd).2).2.1
  have hlt : d < chenQuotientRowLevel Q b := by exact_mod_cast hactive
  exact (lt_chenQuotientRowLevel_iff hb).mp hlt

/-- The upper coefficients retain the exact original sieve product. -/
theorem currentChenQuotientUpperRosserActive_divisor
    {N b cap Q d : ℕ} {z : ℝ} (hzcap : z ≤ (cap : ℝ))
    (hd : d ∈ currentChenQuotientUpperRosserActive N b cap Q z) :
    d ∈ (sieveProduct N (Nat.ceil z)).divisors := by
  have hds := (Finset.mem_filter.mp hd).1
  change d ∈ (actualSmallPrimeProduct N cap z).divisors at hds
  rwa [currentChen_actualSmallPrimeProduct_eq_sieveProduct N cap z hzcap] at hds

/-- Restricting to the nonzero upper coefficients is an exact equality. -/
theorem currentChen_quotientUpperRosser_sum_eq_active
    (N b cap Q : ℕ) (z : ℝ) (f : ℕ → ℝ) :
    (∑ d ∈ actualSmallRosserSupport N cap z,
      actualSmallRosserPlus N cap z (chenQuotientRowLevel Q b : ℝ) d * f d) =
      ∑ d ∈ currentChenQuotientUpperRosserActive N b cap Q z,
        actualSmallRosserPlus N cap z (chenQuotientRowLevel Q b : ℝ) d * f d := by
  simp only [currentChenQuotientUpperRosserActive, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d _
  by_cases h : actualSmallRosserPlus N cap z (chenQuotientRowLevel Q b : ℝ) d = 0
  · simp only [h, ne_eq, not_true_eq_false, if_false, zero_mul]
  · simp only [h, ne_eq, not_false_eq_true, if_true]

end

end ImbalancedChen
