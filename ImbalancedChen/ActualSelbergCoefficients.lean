import ImbalancedChen.FiniteSieveEuler
import ImbalancedChen.WeightedSieveLogBudget
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Explicit finite Selberg coefficients with a proved unit bound

The normalizer and coefficients use the genuine `BoundingSieve.selbergTerms`.
For `L ≥ 1`, the normalizer is positive because its finite sum contains
the unit term.
The standard coefficient formula is supported on allowed divisors at most
`L`, is normalized at one, and has absolute value at most one.

The coefficient bound is an elementary finite argument: multiplying every
coprime tail index `j` by every divisor `e` of `d` injects its numerator
into the normalizer. Recovering `e` as `gcd (j * e) d` proves injectivity.
No coefficient estimate or asymptotic sieve assertion is a hypothesis.
The main quadratic form is not evaluated in this file.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators

/-- The literal finite Selberg normalizer, including the unit term. -/
def finiteSelbergNormalizer (s : BoundingSieve) (L : ℕ) : ℝ :=
  ∑ d ∈ s.prodPrimes.divisors with d ≤ L, s.selbergTerms d

/-- The coprime tail in the standard finite Selberg coefficient formula.
Using `d * j ≤ L` keeps the natural cutoff exact. -/
def finiteSelbergCoprimeSum (s : BoundingSieve) (L d : ℕ) : ℝ :=
  ∑ j ∈ s.prodPrimes.divisors with Nat.Coprime j d ∧ d * j ≤ L,
    s.selbergTerms j

/-- The standard finite Selberg coefficient formula, zero away from its
literal allowed support. -/
def finiteSelbergWeight (s : BoundingSieve) (L d : ℕ) : ℝ :=
  if d ∣ s.prodPrimes ∧ d ≤ L then
    (ArithmeticFunction.moebius d : ℝ) * (s.selbergTerms d / s.nu d) *
      finiteSelbergCoprimeSum s L d / finiteSelbergNormalizer s L
  else 0

@[simp] theorem finiteSelbergTerms_one (s : BoundingSieve) :
    s.selbergTerms 1 = 1 :=
  (BoundingSieve.selbergTerms_isMultiplicative (s := s)).1

/-- The unit term gives a uniform lower bound without any analytic input. -/
theorem one_le_finiteSelbergNormalizer (s : BoundingSieve) {L : ℕ}
    (hL : 1 ≤ L) : 1 ≤ finiteSelbergNormalizer s L := by
  rw [← finiteSelbergTerms_one s]
  apply Finset.single_le_sum
  · intro d hd
    exact (BoundingSieve.selbergTerms_pos (s := s)
      (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1)).le
  · exact Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr ⟨one_dvd _, BoundingSieve.prodPrimes_ne_zero (s := s)⟩,
        hL⟩

theorem finiteSelbergNormalizer_pos (s : BoundingSieve) {L : ℕ}
    (hL : 1 ≤ L) : 0 < finiteSelbergNormalizer s L :=
  lt_of_lt_of_le zero_lt_one (one_le_finiteSelbergNormalizer s hL)

theorem finiteSelbergCoprimeSum_nonneg (s : BoundingSieve) (L d : ℕ) :
    0 ≤ finiteSelbergCoprimeSum s L d := by
  apply Finset.sum_nonneg
  intro j hj
  exact (BoundingSieve.selbergTerms_pos (s := s)
    (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hj).1)).le

@[simp] theorem finiteSelbergCoprimeSum_one (s : BoundingSieve) (L : ℕ) :
    finiteSelbergCoprimeSum s L 1 = finiteSelbergNormalizer s L := by
  simp [finiteSelbergCoprimeSum, finiteSelbergNormalizer]

@[simp] theorem finiteSelbergWeight_one (s : BoundingSieve) {L : ℕ}
    (hL : 1 ≤ L) : finiteSelbergWeight s L 1 = 1 := by
  have hG := (finiteSelbergNormalizer_pos s hL).ne'
  simp [finiteSelbergWeight, hL, s.nu_mult.1, hG]

theorem finiteSelbergWeight_eq_zero_of_not_dvd (s : BoundingSieve)
    (L d : ℕ) (hd : ¬d ∣ s.prodPrimes) : finiteSelbergWeight s L d = 0 := by
  simp [finiteSelbergWeight, hd]

theorem finiteSelbergWeight_eq_zero_of_level (s : BoundingSieve)
    (L d : ℕ) (hd : L < d) : finiteSelbergWeight s L d = 0 := by
  simp [finiteSelbergWeight, Nat.not_le_of_lt hd]

/-- Mathlib's divisor identity in the local-divisor form needed below. -/
theorem sum_divisors_finiteSelbergTerms (s : BoundingSieve) {d : ℕ}
    (hd : d ∣ s.prodPrimes) :
    (∑ e ∈ d.divisors, s.selbergTerms e) = s.selbergTerms d / s.nu d := by
  have h := BoundingSieve.sum_divisors_selbergTerms_eq_selbergTerms_mul_nu_inv
    (s := s) hd
  rw [← Finset.sum_filter,
    Nat.divisors_filter_dvd_of_dvd (BoundingSieve.prodPrimes_ne_zero (s := s)) hd] at h
  simpa only [div_eq_mul_inv] using h

/-- The complete nonnegative coefficient numerator embeds into the
normalizer. The only structural requirement is `d ∣ P`. -/
theorem finiteSelbergNumerator_le_normalizer (s : BoundingSieve) (L : ℕ)
    {d : ℕ} (hd : d ∣ s.prodPrimes) :
    (s.selbergTerms d / s.nu d) * finiteSelbergCoprimeSum s L d ≤
      finiteSelbergNormalizer s L := by
  classical
  let J := s.prodPrimes.divisors.filter
    (fun j : ℕ => Nat.Coprime j d ∧ d * j ≤ L)
  let E := d.divisors ×ˢ J
  let f : ℕ × ℕ → ℕ := fun x => x.2 * x.1
  have hdpos : 0 < d := Nat.pos_of_ne_zero
    (ne_zero_of_dvd_ne_zero (BoundingSieve.prodPrimes_ne_zero (s := s)) hd)
  have hJ : ∀ j ∈ J, j ∣ s.prodPrimes ∧ Nat.Coprime j d ∧ d * j ≤ L := by
    intro j hj
    exact ⟨Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hj).1,
      (Finset.mem_filter.mp hj).2⟩
  have hinj : Set.InjOn f E := by
    intro a ha b hb hab
    obtain ⟨hae, haj⟩ := Finset.mem_product.mp ha
    obtain ⟨hbe, hbj⟩ := Finset.mem_product.mp hb
    have hea : a.1 ∣ d := Nat.dvd_of_mem_divisors hae
    have heb : b.1 ∣ d := Nat.dvd_of_mem_divisors hbe
    have he : a.1 = b.1 := by
      calc
        a.1 = Nat.gcd (f a) d :=
          (Nat.gcd_mul_of_coprime_of_dvd (hJ a.2 haj).2.1 hea).symm
        _ = Nat.gcd (f b) d := congrArg (fun n : ℕ => Nat.gcd n d) hab
        _ = b.1 := Nat.gcd_mul_of_coprime_of_dvd (hJ b.2 hbj).2.1 heb
    have hbpos : 0 < b.1 := Nat.pos_of_mem_divisors hbe
    have hj : a.2 = b.2 := by
      apply Nat.eq_of_mul_eq_mul_right hbpos
      simpa only [f, he] using hab
    exact Prod.ext he hj
  have hsub : E.image f ⊆ s.prodPrimes.divisors.filter (fun k : ℕ => k ≤ L) := by
    intro k hk
    obtain ⟨⟨e, j⟩, hej, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨he, hj⟩ := Finset.mem_product.mp hej
    have hed : e ∣ d := Nat.dvd_of_mem_divisors he
    have heP : e ∣ s.prodPrimes := hed.trans hd
    have hjinfo := hJ j hj
    have hje : Nat.Coprime j e := hjinfo.2.1.of_dvd_right hed
    apply Finset.mem_filter.mpr
    refine ⟨Nat.mem_divisors.mpr
      ⟨hje.mul_dvd_of_dvd_of_dvd hjinfo.1 heP,
        BoundingSieve.prodPrimes_ne_zero (s := s)⟩, ?_⟩
    change j * e ≤ L
    calc
      j * e ≤ j * d := Nat.mul_le_mul_left j (Nat.le_of_dvd hdpos hed)
      _ = d * j := Nat.mul_comm _ _
      _ ≤ L := hjinfo.2.2
  calc
    (s.selbergTerms d / s.nu d) * finiteSelbergCoprimeSum s L d =
        ∑ x ∈ E, s.selbergTerms x.1 * s.selbergTerms x.2 := by
      rw [← sum_divisors_finiteSelbergTerms s hd]
      dsimp only [finiteSelbergCoprimeSum, E, J]
      rw [Finset.sum_product, Finset.sum_mul_sum]
    _ = ∑ x ∈ E, s.selbergTerms (f x) := by
      apply Finset.sum_congr rfl
      intro x hx
      obtain ⟨he, hj⟩ := Finset.mem_product.mp hx
      have hcop : Nat.Coprime x.2 x.1 :=
        (hJ x.2 hj).2.1.of_dvd_right (Nat.dvd_of_mem_divisors he)
      rw [show f x = x.2 * x.1 from rfl,
        BoundingSieve.selbergTerms_isMultiplicative.map_mul_of_coprime hcop,
        mul_comm]
    _ = ∑ k ∈ E.image f, s.selbergTerms k := (Finset.sum_image hinj).symm
    _ ≤ finiteSelbergNormalizer s L := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro k hk _
      exact (BoundingSieve.selbergTerms_pos (s := s)
        (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hk).1)).le

/-- The actual finite formula is bounded by one; the bound is proved,
not supplied as a coefficient hypothesis. -/
theorem abs_finiteSelbergWeight_le_one (s : BoundingSieve) {L : ℕ}
    (hL : 1 ≤ L) (d : ℕ) : |finiteSelbergWeight s L d| ≤ 1 := by
  classical
  by_cases hd : d ∣ s.prodPrimes ∧ d ≤ L
  · have hG := finiteSelbergNormalizer_pos s hL
    have hnu := BoundingSieve.nu_pos_of_dvd_prodPrimes (s := s) hd.1
    have hh := BoundingSieve.selbergTerms_pos (s := s) hd.1
    have hmu : |(ArithmeticFunction.moebius d : ℝ)| = 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_eq_one_of_squarefree
        (BoundingSieve.squarefree_of_dvd_prodPrimes (s := s) hd.1)
    rw [finiteSelbergWeight, if_pos hd, abs_div, abs_mul, abs_mul,
      hmu, one_mul, abs_of_nonneg (div_nonneg hh.le hnu.le),
      abs_of_nonneg (finiteSelbergCoprimeSum_nonneg s L d), abs_of_pos hG]
    exact (div_le_one hG).mpr (finiteSelbergNumerator_le_normalizer s L hd.1)
  · simp [finiteSelbergWeight, hd]

/-- The explicit normalized formula gives a genuine upper-Moebius sieve. -/
theorem upperMoebius_finiteSelbergWeight (s : BoundingSieve) {L : ℕ}
    (hL : 1 ≤ L) :
    BoundingSieve.IsUpperMoebius (BoundingSieve.lambdaSquared (finiteSelbergWeight s L)) :=
  BoundingSieve.upperMoebius_lambdaSquared _ (finiteSelbergWeight_one s hL)

/-- The actual source's normalizer is the literal reciprocal-`p-2` sum. -/
theorem halfProduct_finiteSelbergNormalizer
    (num den N : ℕ) (T : ℝ) (z L : ℕ) (hN : Even N) :
    finiteSelbergNormalizer (halfProductBoundingSieve num den N T z hN) L =
      ∑ d ∈ (sieveProduct N z).divisors with d ≤ L,
        ∏ p ∈ d.primeFactors, 1 / ((p : ℝ) - 2) := by
  unfold finiteSelbergNormalizer
  apply Finset.sum_congr rfl
  intro d hd
  exact halfProductBoundingSieve_selbergTerms num den N T z d hN
    (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1)

/-- The actual allowed coefficient, with both the reciprocal-totient
density and every Selberg term written explicitly. -/
theorem halfProduct_finiteSelbergWeight_formula
    (num den N : ℕ) (T : ℝ) (z L d : ℕ) (hN : Even N)
    (hd : d ∣ sieveProduct N z) (hdL : d ≤ L) :
    finiteSelbergWeight (halfProductBoundingSieve num den N T z hN) L d =
      (ArithmeticFunction.moebius d : ℝ) *
        ((∏ p ∈ d.primeFactors, 1 / ((p : ℝ) - 2)) * (Nat.totient d : ℝ)) *
        (∑ j ∈ (sieveProduct N z).divisors with Nat.Coprime j d ∧ d * j ≤ L,
          ∏ p ∈ j.primeFactors, 1 / ((p : ℝ) - 2)) /
        (∑ j ∈ (sieveProduct N z).divisors with j ≤ L,
          ∏ p ∈ j.primeFactors, 1 / ((p : ℝ) - 2)) := by
  have htail : finiteSelbergCoprimeSum
      (halfProductBoundingSieve num den N T z hN) L d =
      ∑ j ∈ (sieveProduct N z).divisors with Nat.Coprime j d ∧ d * j ≤ L,
        ∏ p ∈ j.primeFactors, 1 / ((p : ℝ) - 2) := by
    unfold finiteSelbergCoprimeSum
    apply Finset.sum_congr rfl
    intro j hj
    exact halfProductBoundingSieve_selbergTerms num den N T z j hN
      (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hj).1)
  rw [finiteSelbergWeight, if_pos ⟨hd, hdL⟩,
    halfProductBoundingSieve_selbergTerms num den N T z d hN hd,
    htail, halfProduct_finiteSelbergNormalizer]
  change _ * (_ / (1 / (Nat.totient d : ℝ))) * _ / _ = _
  rw [div_div_eq_mul_div, div_one]

/-- For the actual source, the proved unit bound pays the weighted-error
cost with `J = 0`: only sixteen extra logarithmic powers are required. -/
theorem halfProduct_finiteSelbergWeight_errSum_sq_le_of_unweighted_logBound
    (num den N : ℕ) (T : ℝ) (z : ℕ) (hN : Even N)
    (hnum : 0 < num) (hden : 0 < den) (hT : 0 < T)
    (hcap : (z : ℝ) ≤ T ^ (((num : ℝ) / (den : ℝ)) /
      (1 + (num : ℝ) / (den : ℝ))))
    (L A : ℕ) (hL : 1 ≤ L) (hlevel : L * L ≤ N)
    (hN1 : 1 ≤ (N : ℝ)) (hlog : 1 ≤ Real.log (N : ℝ))
    (C : ℝ) (hC : 0 ≤ C)
    (hdistribution :
      (∑ d ∈ Finset.Icc 1 (L * L) with Nat.Coprime d N,
        |halfProductCongruenceMass num den N T d -
          halfProductCoprimeMass num den N T d / (Nat.totient d : ℝ)|) ≤
        C * (N : ℝ) / (Real.log (N : ℝ)) ^ (2 * A + 16)) :
    ((halfProductBoundingSieve num den N T z hN).errSum
      (BoundingSieve.lambdaSquared
        (finiteSelbergWeight (halfProductBoundingSieve num den N T z hN) L))) ^ 2 ≤
      3 * (8 : ℝ) ^ 16 * C * (N : ℝ) ^ 2 /
        (Real.log (N : ℝ)) ^ (2 * A) := by
  let s := halfProductBoundingSieve num den N T z hN
  apply halfProductBoundingSieve_errSum_lambdaSquared_sq_le_of_unweighted_logBound
    num den N T z hN hnum hden hT hcap (finiteSelbergWeight s L) L A 0 hlevel
    (fun d hd => finiteSelbergWeight_eq_zero_of_level s L d hd) hN1 hlog
  · intro d _
    simpa only [pow_zero] using abs_finiteSelbergWeight_le_one s hL d
  · exact hC
  · simpa only [Nat.mul_zero, Nat.add_zero] using hdistribution

end

end ImbalancedChen
