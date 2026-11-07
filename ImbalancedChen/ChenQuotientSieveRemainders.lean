import ImbalancedChen.ChenQuotientPrimeSource

/-!
# Genuine quotient sieves and their literal prime-AP remainders

The multiplier is required to be coprime to the actual strict sieve
product. This gate is proved for every selected multiplier in Upsilon 3–6.
The source, unit weights, and total mass are the literal finite objects.
The reciprocal-totient density is used only on allowed sieve divisors;
no density statement for a divisor sharing a prime with the multiplier
is asserted.

Both centre-prime corrections are retained. Even if `b > 1` and
`Coprime b N`, the centre-prime correction need not vanish: at `N = 30`,
`b = 7`, the centre prime `2` lies in the selected progression.
The comparison main term is an arbitrary real number. No distribution
estimate, main sieve bound, or eventual assertion is an input or output.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators
open Classical

/-- Prime factors at the real lower endpoint survive the strict sieve
cap. This includes equality and needs no positivity assumption on `A`. -/
theorem chen_rough_multiplier_coprime_sieveProduct {N b : ℕ} {A : ℝ}
    (hb : ChenPrimeRough A b) :
    Nat.Coprime b (sieveProduct N (Nat.ceil A)) := by
  unfold sieveProduct
  apply Nat.coprime_prod_right_iff.mpr
  intro p hp
  obtain ⟨hpA, hprime, _⟩ := mem_sievePrimes_chen_real_cap.mp hp
  exact (hprime.coprime_iff_not_dvd.mpr
    (fun hpb => (not_lt_of_ge (hb p hprime hpb)) hpA)).symm

/-- A selected prime is coprime to the strict sieve product, including
when it is exactly the real lower endpoint. -/
theorem chen_prime_coprime_sieveProduct_of_real_lower {N p : ℕ} {A : ℝ}
    (hp : Nat.Prime p) (hA : A ≤ (p : ℝ)) :
    Nat.Coprime p (sieveProduct N (Nat.ceil A)) := by
  apply chen_rough_multiplier_coprime_sieveProduct
  intro q hq hqp
  have hqp' : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp hqp
  simpa only [hqp'] using hA

/-- A finite selected product has the required coprimality whenever each
factor is prime and at least the cutoff. No pair ordering is needed. -/
theorem chen_prime_product_coprime_sieveProduct {α : Type*}
    (T : Finset α) (p : α → ℕ) (N : ℕ) (A : ℝ)
    (hT : ∀ t ∈ T, Nat.Prime (p t) ∧ A ≤ (p t : ℝ)) :
    Nat.Coprime (∏ t ∈ T, p t) (sieveProduct N (Nat.ceil A)) := by
  apply Nat.coprime_prod_left_iff.mpr
  intro t ht
  exact chen_prime_coprime_sieveProduct_of_real_lower (hT t ht).1 (hT t ht).2

/-- The two one-prime terms have positive, centre-coprime, sieve-coprime
multipliers, proved from their actual selector membership. -/
theorem chenSinglePrimeSelector_sieve_data {N p : ℕ} {A U : ℝ}
    (hp : p ∈ chenSinglePrimeSelector N A U) :
    1 < p ∧ Nat.Coprime p N ∧
      Nat.Coprime p (sieveProduct N (Nat.ceil A)) := by
  obtain ⟨hc, hA, _⟩ := Finset.mem_filter.mp hp
  obtain ⟨_, hprime, hcop⟩ := mem_chenAdditivePrimeCarrier.mp hc
  exact ⟨hprime.one_lt, hcop,
    chen_prime_coprime_sieveProduct_of_real_lower hprime hA⟩

/-- The fifth term's actual ordered pair satisfies the gate. The strict
order supplies the second factor's inclusive real lower bound. -/
theorem chenY5PrimeSelector_sieve_data {N : ℕ} {t : ℕ × ℕ} {A H : ℝ}
    (ht : t ∈ chenY5PrimeSelector N A H) :
    1 < t.1 * t.2 ∧ Nat.Coprime (t.1 * t.2) N ∧
      Nat.Coprime (t.1 * t.2) (sieveProduct N (Nat.ceil A)) := by
  obtain ⟨hc, hA, hlt, _⟩ := Finset.mem_filter.mp ht
  obtain ⟨hc₁, hc₂⟩ := Finset.mem_product.mp hc
  obtain ⟨_, hp₁, hN₁⟩ := mem_chenAdditivePrimeCarrier.mp hc₁
  obtain ⟨_, hp₂, hN₂⟩ := mem_chenAdditivePrimeCarrier.mp hc₂
  have hA₂ : A ≤ (t.2 : ℝ) := hA.trans (by exact_mod_cast hlt.le)
  refine ⟨?_, Nat.coprime_mul_iff_left.mpr ⟨hN₁, hN₂⟩,
    Nat.coprime_mul_iff_left.mpr
      ⟨chen_prime_coprime_sieveProduct_of_real_lower hp₁ hA,
        chen_prime_coprime_sieveProduct_of_real_lower hp₂ hA₂⟩⟩
  have h₁ := hp₁.two_le
  have h₂ := hp₂.two_le
  nlinarith

/-- The sixth term retains equality at the second-prime lower endpoint.
Its literal bands imply both factors are at least the sieve cutoff. -/
theorem chenY6PrimeSelector_sieve_data {N : ℕ} {t : ℕ × ℕ} {A H D : ℝ}
    (ht : t ∈ chenY6PrimeSelector N A H D) :
    1 < t.1 * t.2 ∧ Nat.Coprime (t.1 * t.2) N ∧
      Nat.Coprime (t.1 * t.2) (sieveProduct N (Nat.ceil A)) := by
  obtain ⟨hc, hA, hH₁, hH₂, _⟩ := Finset.mem_filter.mp ht
  obtain ⟨hc₁, hc₂⟩ := Finset.mem_product.mp hc
  obtain ⟨_, hp₁, hN₁⟩ := mem_chenAdditivePrimeCarrier.mp hc₁
  obtain ⟨_, hp₂, hN₂⟩ := mem_chenAdditivePrimeCarrier.mp hc₂
  have hA₂ : A ≤ (t.2 : ℝ) := hA.trans (hH₁.le.trans hH₂)
  refine ⟨?_, Nat.coprime_mul_iff_left.mpr ⟨hN₁, hN₂⟩,
    Nat.coprime_mul_iff_left.mpr
      ⟨chen_prime_coprime_sieveProduct_of_real_lower hp₁ hA,
        chen_prime_coprime_sieveProduct_of_real_lower hp₂ hA₂⟩⟩
  have h₁ := hp₁.two_le
  have h₂ := hp₂.two_le
  nlinarith

/-- The coprimality actually needed for totient multiplication follows
from the gate and the divisor used by the finite sieve. -/
theorem chenQuotient_allowed_coprime {N b d : ℕ} {A : ℝ}
    (hb : Nat.Coprime b (sieveProduct N (Nat.ceil A)))
    (hd : d ∣ sieveProduct N (Nat.ceil A)) : Nat.Coprime b d :=
  (hb.symm.of_dvd_left hd).symm

/-- The original additive-prime residue is primitive modulo the full
product modulus on actual selected fibres, not merely modulo `d`. -/
theorem chenQuotient_allowed_primitive {N b d : ℕ} {A : ℝ}
    (hbN : Nat.Coprime b N) (hd : d ∣ sieveProduct N (Nat.ceil A)) :
    Nat.Coprime N (b * d) :=
  (Nat.coprime_mul_iff_left.mpr ⟨hbN, coprime_of_dvd_sieveProduct hd⟩).symm

/-- A genuine finite Mathlib sieve for a permitted selected multiplier.
The gate is part of the interface, so the reciprocal-totient density
cannot silently be assigned to arbitrary overlapping multipliers. -/
def chenQuotientBoundingSieve (N b : ℕ) (A : ℝ) (hN : Even N)
    (_hb : Nat.Coprime b (sieveProduct N (Nat.ceil A))) : BoundingSieve where
  support := chenQuotientPrimeSource N b
  prodPrimes := sieveProduct N (Nat.ceil A)
  prodPrimes_squarefree := sieveProduct_squarefree N (Nat.ceil A)
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := ((chenQuotientPrimeSource N b).card : ℝ)
  nu := halfProductDensity
  nu_mult := halfProductDensity_isMultiplicative
  nu_pos_of_prime := fun _ hp _ => halfProductDensity_pos_of_prime hp
  nu_lt_one_of_prime := fun _ hp hd =>
    halfProductDensity_lt_one_of_prime hp (two_lt_prime_of_dvd_sieveProduct hN hp hd)

/-- For a positive selected multiplier, the density at an allowed
divisor is the actual multiplicative totient ratio. This equality is
not asserted for an arbitrary divisor sharing primes with `b`. -/
theorem chenQuotientBoundingSieve_nu_allowed_ratio (N b : ℕ) (A : ℝ)
    (hN : Even N) (hb : Nat.Coprime b (sieveProduct N (Nat.ceil A)))
    (hbpos : 0 < b) {d : ℕ} (hd : d ∣ sieveProduct N (Nat.ceil A)) :
    (chenQuotientBoundingSieve N b A hN hb).nu d =
      (Nat.totient b : ℝ) / (Nat.totient (b * d) : ℝ) := by
  have hphi : (Nat.totient b : ℝ) ≠ 0 :=
    (Nat.cast_pos.mpr (Nat.totient_pos.mpr hbpos)).ne'
  change 1 / (Nat.totient d : ℝ) = _
  rw [Nat.totient_mul (chenQuotient_allowed_coprime hb hd), Nat.cast_mul]
  symm
  calc
    (Nat.totient b : ℝ) / ((Nat.totient b : ℝ) * (Nat.totient d : ℝ)) =
        ((Nat.totient b : ℝ) * (Nat.totient b : ℝ)⁻¹) *
          (Nat.totient d : ℝ)⁻¹ := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = 1 / (Nat.totient d : ℝ) := by
      rw [mul_inv_cancel₀ hphi]
      simp only [one_mul, one_div]

theorem chenQuotientBoundingSieve_totalMass_eq_sum (N b : ℕ) (A : ℝ)
    (hN : Even N) (hb : Nat.Coprime b (sieveProduct N (Nat.ceil A))) :
    (chenQuotientBoundingSieve N b A hN hb).totalMass =
      ∑ q ∈ (chenQuotientBoundingSieve N b A hN hb).support,
        (chenQuotientBoundingSieve N b A hN hb).weights q := by
  simp [chenQuotientBoundingSieve]

/-- The total mass includes the exact centre-prime subtraction even for
positive, centre-coprime selected multipliers. -/
theorem chenQuotientBoundingSieve_totalMass (N b : ℕ) (A : ℝ)
    (hN : Even N) (hb : Nat.Coprime b (sieveProduct N (Nat.ceil A))) :
    (chenQuotientBoundingSieve N b A hN hb).totalMass =
      chenPrimeAPCount N N b - chenCentrePrimeAPCount N N b :=
  chenQuotientPrimeSource_card_cast N b

theorem chenQuotientBoundingSieve_siftedSum (N b : ℕ) (A : ℝ)
    (hN : Even N) (hb : Nat.Coprime b (sieveProduct N (Nat.ceil A))) :
    (chenQuotientBoundingSieve N b A hN hb).siftedSum =
      ((chenSiftedQuotientPrimeSource N b A).card : ℝ) := by
  change (∑ q ∈ chenQuotientPrimeSource N b,
      if Nat.Coprime (sieveProduct N (Nat.ceil A)) q then (1 : ℝ) else 0) = _
  simp_rw [@Nat.coprime_comm (sieveProduct N (Nat.ceil A))]
  rw [← Finset.sum_filter, chenSiftedQuotientPrimeSource_eq_coprime_filter]
  simp

/-- The fibre formula is valid for every natural `d`. Only later
reciprocal-totient cancellation restricts to actual allowed divisors. -/
theorem chenQuotientBoundingSieve_multSum (N b : ℕ) (A : ℝ)
    (hN : Even N) (hb : Nat.Coprime b (sieveProduct N (Nat.ceil A))) (d : ℕ) :
    (chenQuotientBoundingSieve N b A hN hb).multSum d =
      chenPrimeAPCount N N (b * d) - chenCentrePrimeAPCount N N (b * d) := by
  change (∑ q ∈ chenQuotientPrimeSource N b,
      if d ∣ q then (1 : ℝ) else 0) = _
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  exact chenQuotientPrimeSource_divisibility_fibre_card N b d

/-- The exact remainder uses the actual mass and both actual correction
counts. No prime-AP approximation occurs in this theorem. -/
theorem chenQuotientBoundingSieve_rem (N b : ℕ) (A : ℝ)
    (hN : Even N) (hb : Nat.Coprime b (sieveProduct N (Nat.ceil A))) (d : ℕ) :
    (chenQuotientBoundingSieve N b A hN hb).rem d =
      chenPrimeAPCount N N (b * d) - chenCentrePrimeAPCount N N (b * d) -
        (chenPrimeAPCount N N b - chenCentrePrimeAPCount N N b) /
          (Nat.totient d : ℝ) := by
  rw [BoundingSieve.rem, chenQuotientBoundingSieve_multSum,
    chenQuotientBoundingSieve_totalMass]
  change chenPrimeAPCount N N (b * d) - chenCentrePrimeAPCount N N (b * d) -
    (1 / (Nat.totient d : ℝ)) *
      (chenPrimeAPCount N N b - chenCentrePrimeAPCount N N b) = _
  ring

@[simp] theorem chenQuotientBoundingSieve_rem_one (N b : ℕ) (A : ℝ)
    (hN : Even N) (hb : Nat.Coprime b (sieveProduct N (Nat.ceil A))) :
    (chenQuotientBoundingSieve N b A hN hb).rem 1 = 0 := by
  rw [chenQuotientBoundingSieve_rem]
  simp

/-- An empty source is a genuine zero-mass sieve at every modulus. -/
theorem chenQuotientBoundingSieve_rem_of_source_empty (N b : ℕ) (A : ℝ)
    (hN : Even N) (hb : Nat.Coprime b (sieveProduct N (Nat.ceil A)))
    (hempty : chenQuotientPrimeSource N b = ∅) (d : ℕ) :
    (chenQuotientBoundingSieve N b A hN hb).rem d = 0 := by
  rw [BoundingSieve.rem]
  change (∑ q ∈ chenQuotientPrimeSource N b,
      if d ∣ q then (1 : ℝ) else 0) -
        halfProductDensity d * ((chenQuotientPrimeSource N b).card : ℝ) = 0
  simp [hempty]

/-- Ordinary inclusive prime-AP error for an arbitrary real comparison
mass. This is a definition of an error, not a bound or a supplier axiom. -/
def chenQuotientPrimeAPError (N : ℕ) (M : ℝ) (k : ℕ) : ℝ :=
  chenPrimeAPCount N N k - M / (Nat.totient k : ℝ)

/-- The signed centre-prime correction forced by exact total mass. -/
def chenQuotientCentreCorrection (N b d : ℕ) : ℝ :=
  chenCentrePrimeAPCount N N b / (Nat.totient d : ℝ) -
    chenCentrePrimeAPCount N N (b * d)

/-- The positive cost that pays for both actual centre-prime counts. -/
def chenQuotientCentreCost (N b d : ℕ) : ℝ :=
  chenCentrePrimeAPCount N N b / (Nat.totient d : ℝ) +
    chenCentrePrimeAPCount N N (b * d)

private theorem chenQuotient_centre_nonneg (N k : ℕ) :
    0 ≤ chenCentrePrimeAPCount N N k := by
  unfold chenCentrePrimeAPCount
  exact Nat.cast_nonneg _

/-- The selected-modulus main terms cancel exactly by coprimality.
There is no hidden replacement of the centre-prime subtraction by zero. -/
theorem chenQuotientBoundingSieve_rem_eq_primeAP_errors
    (N b : ℕ) (A : ℝ) (hN : Even N)
    (hb : Nat.Coprime b (sieveProduct N (Nat.ceil A)))
    {d : ℕ} (hd : d ∣ sieveProduct N (Nat.ceil A)) (M : ℝ) :
    (chenQuotientBoundingSieve N b A hN hb).rem d =
      chenQuotientPrimeAPError N M (b * d) -
        chenQuotientPrimeAPError N M b / (Nat.totient d : ℝ) +
          chenQuotientCentreCorrection N b d := by
  rw [chenQuotientBoundingSieve_rem]
  unfold chenQuotientPrimeAPError chenQuotientCentreCorrection
  rw [Nat.totient_mul (chenQuotient_allowed_coprime hb hd), Nat.cast_mul]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

private theorem chenQuotient_abs_sub_le_add (x y : ℝ) : |x - y| ≤ |x| + |y| := by
  have hx₁ := neg_abs_le x
  have hx₂ := le_abs_self x
  have hy₁ := neg_abs_le y
  have hy₂ := le_abs_self y
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem abs_chenQuotientCentreCorrection_le (N b d : ℕ) :
    |chenQuotientCentreCorrection N b d| ≤ chenQuotientCentreCost N b d := by
  have hb := chenQuotient_centre_nonneg N b
  have hbd := chenQuotient_centre_nonneg N (b * d)
  have hdiv : 0 ≤ chenCentrePrimeAPCount N N b / (Nat.totient d : ℝ) :=
    div_nonneg hb (Nat.cast_nonneg _)
  unfold chenQuotientCentreCorrection chenQuotientCentreCost
  simpa only [abs_of_nonneg hdiv, abs_of_nonneg hbd] using
    chenQuotient_abs_sub_le_add
      (chenCentrePrimeAPCount N N b / (Nat.totient d : ℝ))
      (chenCentrePrimeAPCount N N (b * d))

/-- Pointwise transfer to two literal ordinary prime-AP errors and the
explicit positive centre cost. The comparison `M` may be any real number. -/
theorem abs_chenQuotientBoundingSieve_rem_le_primeAP_errors
    (N b : ℕ) (A : ℝ) (hN : Even N)
    (hb : Nat.Coprime b (sieveProduct N (Nat.ceil A)))
    {d : ℕ} (hd : d ∣ sieveProduct N (Nat.ceil A)) (M : ℝ) :
    |(chenQuotientBoundingSieve N b A hN hb).rem d| ≤
      |chenQuotientPrimeAPError N M (b * d)| +
        |chenQuotientPrimeAPError N M b| / (Nat.totient d : ℝ) +
          chenQuotientCentreCost N b d := by
  rw [chenQuotientBoundingSieve_rem_eq_primeAP_errors N b A hN hb hd M]
  calc
    _ ≤ |chenQuotientPrimeAPError N M (b * d) -
          chenQuotientPrimeAPError N M b / (Nat.totient d : ℝ)| +
            |chenQuotientCentreCorrection N b d| := abs_add_le _ _
    _ ≤ (|chenQuotientPrimeAPError N M (b * d)| +
          |chenQuotientPrimeAPError N M b / (Nat.totient d : ℝ)|) +
            chenQuotientCentreCost N b d :=
      add_le_add (chenQuotient_abs_sub_le_add _ _)
        (abs_chenQuotientCentreCorrection_le N b d)
    _ = _ := by
      rw [abs_div, abs_of_nonneg
        (show (0 : ℝ) ≤ (Nat.totient d : ℝ) from Nat.cast_nonneg _)]

/-- The finite summed interface needed by an actual distribution
supplier. Repeated outer multipliers are not collapsed here or later. -/
theorem sum_abs_chenQuotientBoundingSieve_rem_le_primeAP_errors
    (N b : ℕ) (A : ℝ) (hN : Even N)
    (hb : Nat.Coprime b (sieveProduct N (Nat.ceil A)))
    (S : Finset ℕ) (hS : ∀ d ∈ S, d ∣ sieveProduct N (Nat.ceil A)) (M : ℝ) :
    (∑ d ∈ S, |(chenQuotientBoundingSieve N b A hN hb).rem d|) ≤
      (∑ d ∈ S, |chenQuotientPrimeAPError N M (b * d)|) +
        |chenQuotientPrimeAPError N M b| *
          (∑ d ∈ S, 1 / (Nat.totient d : ℝ)) +
            ∑ d ∈ S, chenQuotientCentreCost N b d := by
  calc
    _ ≤ ∑ d ∈ S,
        (|chenQuotientPrimeAPError N M (b * d)| +
          |chenQuotientPrimeAPError N M b| / (Nat.totient d : ℝ) +
            chenQuotientCentreCost N b d) := by
      apply Finset.sum_le_sum
      intro d hd
      exact abs_chenQuotientBoundingSieve_rem_le_primeAP_errors N b A hN hb (hS d hd) M
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum, div_eq_mul_inv, one_mul]

/-- Actual Upsilon 3 is a sum of genuine quotient sieves. Attached
selector labels carry their proved coprimality and preserve multiplicity. -/
theorem chenUpsilon3_eq_quotientBoundingSieve (N : ℕ) (hN : Even N) :
    chenUpsilon3 N =
      ∑ p ∈ (chenSinglePrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ))
          ((N : ℝ) ^ (1 / 3 : ℝ))).attach,
        (chenQuotientBoundingSieve N p.val ((N : ℝ) ^ (100 / 1149 : ℝ)) hN
          (chenSinglePrimeSelector_sieve_data p.property).2.2).siftedSum := by
  rw [chenUpsilon3_eq_siftedQuotientPrimeSource]
  simp_rw [chenQuotientBoundingSieve_siftedSum]
  exact (Finset.sum_attach _ _).symm

/-- The distinct strict upper cap of Upsilon 4 is unchanged. -/
theorem chenUpsilon4_eq_quotientBoundingSieve (N : ℕ) (hN : Even N) :
    chenUpsilon4 N =
      ∑ p ∈ (chenSinglePrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ))
          ((N : ℝ) ^ ((1 / 2 : ℝ) - 3 * (100 / 1149 : ℝ)))).attach,
        (chenQuotientBoundingSieve N p.val ((N : ℝ) ^ (100 / 1149 : ℝ)) hN
          (chenSinglePrimeSelector_sieve_data p.property).2.2).siftedSum := by
  rw [chenUpsilon4_eq_siftedQuotientPrimeSource]
  simp_rw [chenQuotientBoundingSieve_siftedSum]
  exact (Finset.sum_attach _ _).symm

/-- Upsilon 5 keeps the actual ordered pairs as outer labels. -/
theorem chenUpsilon5_eq_quotientBoundingSieve (N : ℕ) (hN : Even N) :
    chenUpsilon5 N =
      ∑ t ∈ (chenY5PrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ))
          ((N : ℝ) ^ (50 / 309 : ℝ))).attach,
        (chenQuotientBoundingSieve N (t.val.1 * t.val.2)
          ((N : ℝ) ^ (100 / 1149 : ℝ)) hN
          (chenY5PrimeSelector_sieve_data t.property).2.2).siftedSum := by
  rw [chenUpsilon5_eq_siftedQuotientPrimeSource]
  simp_rw [chenQuotientBoundingSieve_siftedSum]
  exact (Finset.sum_attach _ _).symm

/-- Upsilon 6 keeps the full half-open second-prime band. -/
theorem chenUpsilon6_eq_quotientBoundingSieve (N : ℕ) (hN : Even N) :
    chenUpsilon6 N =
      ∑ t ∈ (chenY6PrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ))
          ((N : ℝ) ^ (50 / 309 : ℝ))
          ((N : ℝ) ^ ((1 / 2 : ℝ) - 3 * (100 / 1149 : ℝ)))).attach,
        (chenQuotientBoundingSieve N (t.val.1 * t.val.2)
          ((N : ℝ) ^ (100 / 1149 : ℝ)) hN
          (chenY6PrimeSelector_sieve_data t.property).2.2).siftedSum := by
  rw [chenUpsilon6_eq_siftedQuotientPrimeSource]
  simp_rw [chenQuotientBoundingSieve_siftedSum]
  exact (Finset.sum_attach _ _).symm

end

end ImbalancedChen
