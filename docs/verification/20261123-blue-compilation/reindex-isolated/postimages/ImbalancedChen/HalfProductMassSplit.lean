import ImbalancedChen.HalfProductMassFibres

/-!
# A finite high/low envelope for the actual half-product mass

The main theorem compares the literal uncut half-product source with
`sum_{N^alpha < r <= sqrt N, r prime} pi(N / r)`, where
`alpha = num / (num + den)` and `beta = den / (num + den)`.

The discrepancy is bounded by the prime rectangle of sides `N^alpha`
and `N^beta`, plus the prime square of side `sqrt N`. Equality at the
power split is assigned to the low range. The high-range order correction
is exactly `pi(r - 1)`, so prime squares are retained.

Every estimate here is finite and elementary. No prime-number theorem,
asymptotic mass premise, or external project theorem is assumed.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators

/-- The inclusive low side of a split of the smaller prime. -/
def halfProductLowPrimes (N A : ℕ) : Finset ℕ := by
  classical
  exact (Nat.primesLE (Nat.sqrt N)).filter (fun r => r ≤ A)

/-- The strict high side of a split of the smaller prime. -/
def halfProductHighPrimes (N A : ℕ) : Finset ℕ := by
  classical
  exact (Nat.primesLE (Nat.sqrt N)).filter (fun r => A < r)

/-- The high-range prime-prefix approximation, before restoring `r ≤ q`. -/
def halfProductPrimePrefixMass (N A : ℕ) : ℕ :=
  ∑ r ∈ halfProductHighPrimes N A, Nat.primeCounting (N / r)

theorem halfProductLowPrimes_card_le (N A : ℕ) :
    (halfProductLowPrimes N A).card ≤ Nat.primeCounting A := by
  classical
  have hs : halfProductLowPrimes N A ⊆ Nat.primesLE A := by
    intro r hr
    obtain ⟨hr, hrA⟩ := Finset.mem_filter.mp hr
    exact Nat.mem_primesLE.mpr ⟨hrA, (Nat.mem_primesLE.mp hr).2⟩
  exact (Finset.card_le_card hs).trans_eq (Nat.primesLE_card_eq_primeCounting A)

theorem halfProductHighPrimes_card_le (N A : ℕ) :
    (halfProductHighPrimes N A).card ≤ Nat.primeCounting (Nat.sqrt N) := by
  classical
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
    (Nat.primesLE_card_eq_primeCounting (Nat.sqrt N))

/-- Exact partition of the source mass, with the equality boundary low. -/
theorem halfProductSource_card_eq_low_add_high (num den N A : ℕ) :
    (halfProductSource num den N 0).card =
      (∑ r ∈ halfProductLowPrimes N A, (halfProductPrimeFibre num den N r).card) +
      ∑ r ∈ halfProductHighPrimes N A, (halfProductPrimeFibre num den N r).card := by
  classical
  rw [halfProductSource_card_eq_sum_primeFibre]
  simpa only [halfProductLowPrimes, halfProductHighPrimes, not_le] using
    (Finset.sum_filter_add_sum_filter_not (Nat.primesLE (Nat.sqrt N))
      (fun r => r ≤ A) (fun r => (halfProductPrimeFibre num den N r).card)).symm

/-- Any original fibre is a subset of the prime prefix at `N / r`. -/
theorem halfProductPrimeFibre_card_le_prefix (num den N r : ℕ) :
    (halfProductPrimeFibre num den N r).card ≤ Nat.primeCounting (N / r) := by
  classical
  have hs : halfProductPrimeFibre num den N r ⊆ Nat.primesLE (N / r) := by
    intro q hq
    obtain ⟨_, hqN, hprime, _⟩ := mem_halfProductPrimeFibre.mp hq
    exact Nat.mem_primesLE.mpr ⟨hqN, hprime⟩
  exact (Finset.card_le_card hs).trans_eq (Nat.primesLE_card_eq_primeCounting (N / r))

/-- A bound on the larger prime puts an entire fibre inside a prime prefix. -/
theorem halfProductPrimeFibre_card_le_of_bound {num den N r B : ℕ}
    (hB : ∀ q ∈ halfProductPrimeFibre num den N r, q ≤ B) :
    (halfProductPrimeFibre num den N r).card ≤ Nat.primeCounting B := by
  classical
  have hs : halfProductPrimeFibre num den N r ⊆ Nat.primesLE B := by
    intro q hq
    exact Nat.mem_primesLE.mpr ⟨hB q hq, (mem_halfProductPrimeFibre.mp hq).2.2.1⟩
  exact (Finset.card_le_card hs).trans_eq (Nat.primesLE_card_eq_primeCounting B)

/-- When the power condition is automatic, only primes strictly below `r`
are missing. The diagonal prime square is included. -/
theorem halfProductPrimeFibre_card_add_order_loss {num den N r : ℕ}
    (hr : r ∈ Nat.primesLE (Nat.sqrt N))
    (hbad : ∀ q, Nat.Prime q → q ≤ N / r → q ^ num < r ^ den) :
    (halfProductPrimeFibre num den N r).card + Nat.primeCounting (r - 1) =
      Nat.primeCounting (N / r) := by
  classical
  obtain ⟨hrN, hprime⟩ := Nat.mem_primesLE.mp hr
  have heq : halfProductPrimeFibre num den N r =
      (Finset.Icc r (N / r)).filter Nat.Prime := by
    ext q
    simp only [mem_halfProductPrimeFibre, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hrq, hqN, hq, _⟩
      exact ⟨⟨hrq, hqN⟩, hq⟩
    · rintro ⟨⟨hrq, hqN⟩, hq⟩
      exact ⟨hrq, hqN, hq, hbad q hq hqN⟩
  have hself : r ≤ N / r :=
    (Nat.le_div_iff_mul_le hprime.pos).mpr (Nat.le_sqrt.mp hrN)
  rw [heq, card_primes_Icc_eq_primeCounting_sub hprime.pos]
  exact Nat.sub_add_cancel (Nat.monotone_primeCounting ((Nat.sub_le r 1).trans hself))

/-- The low original mass is bounded by a genuine prime rectangle. -/
theorem halfProduct_low_mass_le_rectangle {num den N A B : ℕ}
    (hB : ∀ r ∈ halfProductLowPrimes N A,
      ∀ q ∈ halfProductPrimeFibre num den N r, q ≤ B) :
    (∑ r ∈ halfProductLowPrimes N A, (halfProductPrimeFibre num den N r).card) ≤
      Nat.primeCounting A * Nat.primeCounting B := by
  calc
    (∑ r ∈ halfProductLowPrimes N A, (halfProductPrimeFibre num den N r).card) ≤
        ∑ _r ∈ halfProductLowPrimes N A, Nat.primeCounting B := by
      exact Finset.sum_le_sum (fun r hr => halfProductPrimeFibre_card_le_of_bound (hB r hr))
    _ = (halfProductLowPrimes N A).card * Nat.primeCounting B := by simp
    _ ≤ Nat.primeCounting A * Nat.primeCounting B :=
      Nat.mul_le_mul_right _ (halfProductLowPrimes_card_le N A)

/-- The high prefix exceeds the high source mass by at most the prime square. -/
theorem halfProduct_prefix_le_high_mass_add_square {num den N A : ℕ}
    (hbad : ∀ r ∈ halfProductHighPrimes N A,
      ∀ q, Nat.Prime q → q ≤ N / r → q ^ num < r ^ den) :
    halfProductPrimePrefixMass N A ≤
      (∑ r ∈ halfProductHighPrimes N A, (halfProductPrimeFibre num den N r).card) +
      Nat.primeCounting (Nat.sqrt N) ^ 2 := by
  classical
  have heq : halfProductPrimePrefixMass N A =
      (∑ r ∈ halfProductHighPrimes N A, (halfProductPrimeFibre num den N r).card) +
      ∑ r ∈ halfProductHighPrimes N A, Nat.primeCounting (r - 1) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun r hr =>
      (halfProductPrimeFibre_card_add_order_loss (Finset.mem_filter.mp hr).1
        (hbad r hr)).symm)
  have horder : (∑ r ∈ halfProductHighPrimes N A, Nat.primeCounting (r - 1)) ≤
      Nat.primeCounting (Nat.sqrt N) ^ 2 := by
    calc
      (∑ r ∈ halfProductHighPrimes N A, Nat.primeCounting (r - 1)) ≤
          ∑ _r ∈ halfProductHighPrimes N A, Nat.primeCounting (Nat.sqrt N) := by
        apply Finset.sum_le_sum
        intro r hr
        exact Nat.monotone_primeCounting ((Nat.sub_le r 1).trans
          (Nat.mem_primesLE.mp (Finset.mem_filter.mp hr).1).1)
      _ = (halfProductHighPrimes N A).card * Nat.primeCounting (Nat.sqrt N) := by simp
      _ ≤ Nat.primeCounting (Nat.sqrt N) * Nat.primeCounting (Nat.sqrt N) :=
        Nat.mul_le_mul_right _ (halfProductHighPrimes_card_le N A)
      _ = Nat.primeCounting (Nat.sqrt N) ^ 2 := (pow_two _).symm
  rw [heq]
  exact Nat.add_le_add_left horder _

/-- A purely finite envelope at an arbitrary integer split. Its two
geometric hypotheses are discharged at the power split below. -/
theorem halfProductSource_primePrefix_envelope {num den N A B : ℕ}
    (hB : ∀ r ∈ halfProductLowPrimes N A,
      ∀ q ∈ halfProductPrimeFibre num den N r, q ≤ B)
    (hbad : ∀ r ∈ halfProductHighPrimes N A,
      ∀ q, Nat.Prime q → q ≤ N / r → q ^ num < r ^ den) :
    |((halfProductSource num den N 0).card : ℝ) -
        (halfProductPrimePrefixMass N A : ℝ)| ≤
      (Nat.primeCounting A : ℝ) * Nat.primeCounting B +
        (Nat.primeCounting (Nat.sqrt N) : ℝ) ^ 2 := by
  have hsplit := halfProductSource_card_eq_low_add_high num den N A
  have hlo := halfProduct_low_mass_le_rectangle hB
  have hhi := halfProduct_prefix_le_high_mass_add_square hbad
  have hhigh : (∑ r ∈ halfProductHighPrimes N A,
      (halfProductPrimeFibre num den N r).card) ≤ halfProductPrimePrefixMass N A :=
    Finset.sum_le_sum (fun r _ => halfProductPrimeFibre_card_le_prefix num den N r)
  have hupper : (halfProductSource num den N 0).card ≤
      halfProductPrimePrefixMass N A + Nat.primeCounting A * Nat.primeCounting B := by
    omega
  have hlower : halfProductPrimePrefixMass N A ≤
      (halfProductSource num den N 0).card + Nat.primeCounting (Nat.sqrt N) ^ 2 := by
    omega
  have hupperR : ((halfProductSource num den N 0).card : ℝ) ≤
      (halfProductPrimePrefixMass N A : ℝ) +
        (Nat.primeCounting A : ℝ) * Nat.primeCounting B := by exact_mod_cast hupper
  have hlowerR : (halfProductPrimePrefixMass N A : ℝ) ≤
      ((halfProductSource num den N 0).card : ℝ) +
        (Nat.primeCounting (Nat.sqrt N) : ℝ) ^ 2 := by exact_mod_cast hlower
  have hrect : (0 : ℝ) ≤ (Nat.primeCounting A : ℝ) * Nat.primeCounting B := by positivity
  have hsq : (0 : ℝ) ≤ (Nat.primeCounting (Nat.sqrt N) : ℝ) ^ 2 := sq_nonneg _
  apply abs_le.mpr
  constructor <;> linarith

/-- The lower and upper exponents in the elementary prime rectangle. -/
def halfProductMassAlpha (num den : ℕ) : ℝ := (num : ℝ) / ((num : ℝ) + den)

def halfProductMassBeta (num den : ℕ) : ℝ := (den : ℝ) / ((num : ℝ) + den)

/-- The fixed interval and complementary exponent used by the mass model. -/
theorem halfProductMass_exponents {num den : ℕ}
    (hnum : 0 < num) (hnumden : num < den) :
    0 < halfProductMassAlpha num den ∧
      halfProductMassAlpha num den < 1 / 2 ∧
      0 < halfProductMassBeta num den ∧
      halfProductMassAlpha num den + halfProductMassBeta num den = 1 := by
  have hn : (0 : ℝ) < num := Nat.cast_pos.mpr hnum
  have hnd : (num : ℝ) < den := Nat.cast_lt.mpr hnumden
  have hd : (0 : ℝ) < den := hn.trans hnd
  have hs : (0 : ℝ) < (num : ℝ) + den := add_pos hn hd
  unfold halfProductMassAlpha halfProductMassBeta
  refine ⟨div_pos hn hs, ?_, div_pos hd hs, ?_⟩
  · apply (div_lt_iff₀ hs).mpr
    linarith
  · rw [← add_div, div_self (ne_of_gt hs)]

/-- The natural-floor implementation has exactly the strict real lower
endpoint and the inclusive natural square-root upper endpoint. -/
theorem mem_halfProductHighPrimes_power_iff (num den N r : ℕ) :
    r ∈ halfProductHighPrimes N
        (Nat.floor ((N : ℝ) ^ halfProductMassAlpha num den)) ↔
      (N : ℝ) ^ halfProductMassAlpha num den < (r : ℝ) ∧
        r ≤ Nat.sqrt N ∧ Nat.Prime r := by
  classical
  constructor
  · intro hr
    obtain ⟨hrS, hrA⟩ := Finset.mem_filter.mp hr
    refine ⟨?_, (Nat.mem_primesLE.mp hrS).1, (Nat.mem_primesLE.mp hrS).2⟩
    by_contra hn
    exact (not_le_of_gt hrA) (Nat.le_floor (le_of_not_gt hn))
  · rintro ⟨hlarge, hrN, hr⟩
    refine Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hrN, hr⟩, ?_⟩
    have h := (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N)
      (halfProductMassAlpha num den))).trans_lt hlarge
    exact_mod_cast h

/-- Low smaller primes force a strict larger-prime power bound. -/
theorem halfProduct_low_prime_lt_power {num den N r q : ℕ}
    (hnum : 0 < num)
    (hr : (r : ℝ) ≤ (N : ℝ) ^ halfProductMassAlpha num den)
    (hbad : q ^ num < r ^ den) :
    (q : ℝ) < (N : ℝ) ^ halfProductMassBeta num den := by
  have hn : (num : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hnum)
  have hs : (num : ℝ) + den ≠ 0 := by positivity
  have he : halfProductMassAlpha num den * ((den : ℝ) / num) =
      halfProductMassBeta num den := by
    unfold halfProductMassAlpha halfProductMassBeta
    field_simp [hn, hs] <;> ring
  calc
    (q : ℝ) < (r : ℝ) ^ ((den : ℝ) / num) :=
      (nat_pow_lt_iff_lt_reciprocal_rpow hnum).mp hbad
    _ ≤ ((N : ℝ) ^ halfProductMassAlpha num den) ^ ((den : ℝ) / num) :=
      Real.rpow_le_rpow (Nat.cast_nonneg r) hr
        (div_nonneg (Nat.cast_nonneg den) (Nat.cast_nonneg num))
    _ = (N : ℝ) ^ halfProductMassBeta num den := by
      rw [← Real.rpow_mul (Nat.cast_nonneg N), he]

/-- Above the exact power split, the product bound makes strict badness
automatic. Positivity is enough; no primality or ordering is needed here. -/
theorem halfProduct_high_prime_bad {num den N r q : ℕ}
    (hnum : 0 < num) (hden : 0 < den) (hr : 0 < r) (hq : 0 < q)
    (hprod : r * q ≤ N)
    (hlarge : (N : ℝ) ^ halfProductMassAlpha num den < (r : ℝ)) :
    q ^ num < r ^ den := by
  have hrR : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr ((Nat.mul_pos hr hq).trans_le hprod)
  have hnR : (0 : ℝ) < num := Nat.cast_pos.mpr hnum
  have hdR : (0 : ℝ) < den := Nat.cast_pos.mpr hden
  have hs : (0 : ℝ) < (num : ℝ) + den := add_pos hnR hdR
  have hprodR : (r : ℝ) * (q : ℝ) ≤ (N : ℝ) := by exact_mod_cast hprod
  have hlogProd : Real.log (r : ℝ) + Real.log (q : ℝ) ≤ Real.log (N : ℝ) := by
    have h := Real.log_le_log (mul_pos hrR hqR) hprodR
    simpa only [Real.log_mul (ne_of_gt hrR) (ne_of_gt hqR)] using h
  have hlogLarge : (num : ℝ) * Real.log (N : ℝ) <
      Real.log (r : ℝ) * ((num : ℝ) + den) := by
    have h := (Real.log_lt_log_iff
      (Real.rpow_pos_of_pos hNR (halfProductMassAlpha num den)) hrR).mpr hlarge
    rw [Real.log_rpow hNR, halfProductMassAlpha, div_mul_eq_mul_div] at h
    exact (div_lt_iff₀ hs).mp h
  have hlogPow : Real.log ((q : ℝ) ^ num) < Real.log ((r : ℝ) ^ den) := by
    rw [Real.log_pow, Real.log_pow]
    nlinarith [mul_le_mul_of_nonneg_left hlogProd hnR.le]
  have hp := (Real.log_lt_log_iff (pow_pos hqR num) (pow_pos hrR den)).mp hlogPow
  exact_mod_cast hp

/-- The analytic-facing approximation with the literal strict power window. -/
def halfProductMassApprox (num den N : ℕ) : ℕ :=
  halfProductPrimePrefixMass N (Nat.floor ((N : ℝ) ^ halfProductMassAlpha num den))

/-- Explicit finite envelope for the actual source. The main sum includes
all primes `N^alpha < r ≤ sqrt N`; the low error rectangle includes its
boundary, and the square error accounts only for the order restriction. -/
theorem halfProductSource_mass_split_envelope {num den : ℕ}
    (hnum : 0 < num) (hnumden : num < den) (N : ℕ) :
    |((halfProductSource num den N 0).card : ℝ) -
        (halfProductMassApprox num den N : ℝ)| ≤
      (Nat.primeCounting (Nat.floor ((N : ℝ) ^ halfProductMassAlpha num den)) : ℝ) *
        Nat.primeCounting (Nat.floor ((N : ℝ) ^ halfProductMassBeta num den)) +
      (Nat.primeCounting (Nat.sqrt N) : ℝ) ^ 2 := by
  classical
  unfold halfProductMassApprox
  apply halfProductSource_primePrefix_envelope
  · intro r hr q hq
    have hrle := (Finset.mem_filter.mp hr).2
    have hrR : (r : ℝ) ≤ (N : ℝ) ^ halfProductMassAlpha num den :=
      (Nat.cast_le.mpr hrle).trans
        (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) _))
    apply Nat.le_floor
    exact (halfProduct_low_prime_lt_power hnum hrR
      (mem_halfProductPrimeFibre.mp hq).2.2.2).le
  · intro r hr q hq hqN
    obtain ⟨hrS, hrA⟩ := Finset.mem_filter.mp hr
    have hrprime := (Nat.mem_primesLE.mp hrS).2
    have hlarge : (N : ℝ) ^ halfProductMassAlpha num den < (r : ℝ) := by
      by_contra hn
      exact (not_le_of_gt hrA) (Nat.le_floor (le_of_not_gt hn))
    apply halfProduct_high_prime_bad hnum (hnum.trans hnumden) hrprime.pos hq.pos
      _ hlarge
    simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hrprime.pos).mp hqN

/-- The same approximation for the literal real-cutoff source, with only
its already-proved ceiling loss. This applies in particular to `logCutoff N`. -/
theorem halfProductSource_mass_split_cutoff_envelope {num den : ℕ}
    (hnum : 0 < num) (hnumden : num < den) (N : ℕ) (T : ℝ) :
    |((halfProductSource num den N T).card : ℝ) -
        (halfProductMassApprox num den N : ℝ)| ≤
      (Nat.primeCounting (Nat.floor ((N : ℝ) ^ halfProductMassAlpha num den)) : ℝ) *
        Nat.primeCounting (Nat.floor ((N : ℝ) ^ halfProductMassBeta num den)) +
      (Nat.primeCounting (Nat.sqrt N) : ℝ) ^ 2 + Nat.ceil T := by
  have hmass := abs_le.mp (halfProductSource_mass_split_envelope hnum hnumden N)
  have hpart : ((halfProductSource num den N 0).card : ℝ) =
      ((halfProductSource num den N T).card : ℝ) +
        ((smallHalfProductSource num den N T).card : ℝ) := by
    exact_mod_cast halfProductSource_zero_card_eq_cutoff_add_small num den N T
  have hsmall : ((smallHalfProductSource num den N T).card : ℝ) ≤ (Nat.ceil T : ℝ) := by
    exact_mod_cast smallHalfProductSource_card_le_ceil num den N T
  have hsmall0 : (0 : ℝ) ≤ (smallHalfProductSource num den N T).card := Nat.cast_nonneg _
  have hceil0 : (0 : ℝ) ≤ Nat.ceil T := Nat.cast_nonneg _
  apply abs_le.mpr
  constructor <;> linarith [hmass.1, hmass.2]

end

end ImbalancedChen
