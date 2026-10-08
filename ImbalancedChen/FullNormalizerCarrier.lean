import ImbalancedChen.ActualSelbergCoefficients

/-!
# The full finite carrier of the genuine Selberg normalizer

If the strict prime cap `z` is larger than the inclusive coefficient
cutoff `L`, the divisors of `sieveProduct N z` at most `L` are exactly the
squarefree naturals in `Icc 1 L` coprime to `N`. This carrier statement
needs no evenness or positivity assumption on `N` or `L`.

For even `N`, the genuine `finiteSelbergNormalizer` therefore equals the
full squarefree, coprime reciprocal-`p-2` sum. In particular `z = L + 1`
includes every prime factor of every admissible `d ≤ L`. The unit term
is retained, the zero cutoff gives the empty sum, and the zero center
leaves only the unit term whenever `L ≥ 1`.

These are exact finite identities. No estimate or asymptotic formula for
the normalizer is assumed or proved.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators

/-- Every squarefree natural below the strict cap whose prime factors
avoid `N` divides the literal sieve product. No evenness is needed. -/
theorem dvd_sieveProduct_of_squarefree_coprime_of_lt
    {N z d : ℕ} (hdz : d < z) (hsq : Squarefree d)
    (hcop : Nat.Coprime d N) : d ∣ sieveProduct N z := by
  classical
  have hsub : d.primeFactors ⊆ sievePrimes N z := by
    intro p hp
    have hprime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    have hpd : p ∣ d := Nat.dvd_of_mem_primeFactors hp
    have hpN : Nat.Coprime p N := hcop.of_dvd_left hpd
    exact mem_sievePrimes.mpr
      ⟨lt_of_le_of_lt (Nat.le_of_dvd (Nat.pos_of_ne_zero hsq.ne_zero) hpd) hdz,
        hprime, hprime.coprime_iff_not_dvd.mp hpN⟩
  have hprod := Finset.prod_dvd_prod_of_subset d.primeFactors
    (sievePrimes N z) (fun p : ℕ => p) hsub
  simpa only [Nat.prod_primeFactors_of_squarefree hsq, sieveProduct] using hprod

/-- The inclusive `d ≤ L` carrier equals the full squarefree, coprime
carrier as soon as `L < z`. This also handles `L = 0` and `N = 0`. -/
theorem le_and_dvd_sieveProduct_iff
    {N z L d : ℕ} (hLz : L < z) :
    d ≤ L ∧ d ∣ sieveProduct N z ↔
      1 ≤ d ∧ d ≤ L ∧ Squarefree d ∧ Nat.Coprime d N := by
  constructor
  · rintro ⟨hdL, hdP⟩
    have hsq : Squarefree d :=
      Squarefree.squarefree_of_dvd hdP (sieveProduct_squarefree N z)
    exact ⟨Nat.pos_of_ne_zero hsq.ne_zero, hdL, hsq,
      coprime_of_dvd_sieveProduct hdP⟩
  · rintro ⟨_hdpos, hdL, hsq, hcop⟩
    exact ⟨hdL, dvd_sieveProduct_of_squarefree_coprime_of_lt
      (lt_of_le_of_lt hdL hLz) hsq hcop⟩

/-- Exact equality of finite carriers, including both interval endpoints. -/
theorem sieveProduct_divisors_filter_eq_fullCarrier
    {N z L : ℕ} (hLz : L < z) :
    (sieveProduct N z).divisors.filter (fun d : ℕ => d ≤ L) =
      (Finset.Icc 1 L).filter (fun d : ℕ => Squarefree d ∧ Nat.Coprime d N) := by
  classical
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hdP, _hP⟩, hdL⟩
    obtain ⟨hdpos, hdL, hsq, hcop⟩ :=
      (le_and_dvd_sieveProduct_iff hLz).mp ⟨hdL, hdP⟩
    exact ⟨⟨hdpos, hdL⟩, hsq, hcop⟩
  · rintro ⟨⟨hdpos, hdL⟩, hsq, hcop⟩
    have hdP := (le_and_dvd_sieveProduct_iff hLz).mpr ⟨hdpos, hdL, hsq, hcop⟩
    exact ⟨⟨hdP.2, (sieveProduct_squarefree N z).ne_zero⟩, hdP.1⟩

/-- Choosing the strict cap one above the level includes the level itself. -/
theorem sieveProduct_divisors_succ_filter_eq_fullCarrier (N L : ℕ) :
    (sieveProduct N (L + 1)).divisors.filter (fun d : ℕ => d ≤ L) =
      (Finset.Icc 1 L).filter (fun d : ℕ => Squarefree d ∧ Nat.Coprime d N) :=
  sieveProduct_divisors_filter_eq_fullCarrier (Nat.lt_succ_self L)

/-- The full finite reciprocal-`p-2` sum, with its unit term and literal
squarefree and coprimality conditions. -/
def fullSelbergNormalizer (N L : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 L with Squarefree d ∧ Nat.Coprime d N,
    ∏ p ∈ d.primeFactors, 1 / ((p : ℝ) - 2)

@[simp] theorem fullSelbergNormalizer_zero_level (N : ℕ) :
    fullSelbergNormalizer N 0 = 0 := by
  simp [fullSelbergNormalizer]

@[simp] theorem fullSelbergNormalizer_one_level (N : ℕ) :
    fullSelbergNormalizer N 1 = 1 := by
  simp [fullSelbergNormalizer]

/-- At center zero, coprimality leaves precisely the unit contribution. -/
theorem fullSelbergNormalizer_zero_center {L : ℕ} (hL : 1 ≤ L) :
    fullSelbergNormalizer 0 L = 1 := by
  classical
  have hcarrier : (Finset.Icc 1 L).filter
      (fun d : ℕ => Squarefree d ∧ Nat.Coprime d 0) = {1} := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
    constructor
    · rintro ⟨_hdL, _hsq, hcop⟩
      simpa only [Nat.gcd_zero_right] using hcop.gcd_eq_one
    · intro hd
      subst d
      exact ⟨⟨le_rfl, hL⟩, squarefree_one, Nat.coprime_one_left 0⟩
  unfold fullSelbergNormalizer
  rw [hcarrier]
  simp

/-- The genuine finite normalizer has the full arithmetic carrier once
the strict prime cap exceeds the inclusive level. Evenness is needed
only for the actual reciprocal-totient BoundingSieve and its local terms. -/
theorem halfProduct_finiteSelbergNormalizer_eq_full
    (num den N : ℕ) (T : ℝ) (z L : ℕ) (hN : Even N) (hLz : L < z) :
    finiteSelbergNormalizer (halfProductBoundingSieve num den N T z hN) L =
      fullSelbergNormalizer N L := by
  unfold fullSelbergNormalizer
  rw [halfProduct_finiteSelbergNormalizer,
    sieveProduct_divisors_filter_eq_fullCarrier hLz]

/-- Explicit full-sum form, with no abbreviation for the arithmetic carrier. -/
theorem halfProduct_finiteSelbergNormalizer_full_sum
    (num den N : ℕ) (T : ℝ) (z L : ℕ) (hN : Even N) (hLz : L < z) :
    finiteSelbergNormalizer (halfProductBoundingSieve num den N T z hN) L =
      ∑ d ∈ Finset.Icc 1 L with Squarefree d ∧ Nat.Coprime d N,
        ∏ p ∈ d.primeFactors, 1 / ((p : ℝ) - 2) :=
  halfProduct_finiteSelbergNormalizer_eq_full num den N T z L hN hLz

/-- The canonical strict cap `L + 1` gives the same genuine full sum. -/
theorem halfProduct_finiteSelbergNormalizer_succ_full_sum
    (num den N : ℕ) (T : ℝ) (L : ℕ) (hN : Even N) :
    finiteSelbergNormalizer
        (halfProductBoundingSieve num den N T (L + 1) hN) L =
      ∑ d ∈ Finset.Icc 1 L with Squarefree d ∧ Nat.Coprime d N,
        ∏ p ∈ d.primeFactors, 1 / ((p : ℝ) - 2) :=
  halfProduct_finiteSelbergNormalizer_full_sum
    num den N T (L + 1) L hN (Nat.lt_succ_self L)

/-- Enlarging an already sufficient prime cap does not change the
normalizer at the fixed coefficient level. -/
theorem halfProduct_finiteSelbergNormalizer_cap_independent
    (num den N : ℕ) (T : ℝ) (z₁ z₂ L : ℕ) (hN : Even N)
    (h₁ : L < z₁) (h₂ : L < z₂) :
    finiteSelbergNormalizer (halfProductBoundingSieve num den N T z₁ hN) L =
      finiteSelbergNormalizer (halfProductBoundingSieve num den N T z₂ hN) L := by
  rw [halfProduct_finiteSelbergNormalizer_eq_full num den N T z₁ L hN h₁,
    halfProduct_finiteSelbergNormalizer_eq_full num den N T z₂ L hN h₂]

end

end ImbalancedChen
