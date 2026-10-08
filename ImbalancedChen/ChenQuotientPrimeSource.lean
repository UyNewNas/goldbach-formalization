import ImbalancedChen.ChenInitialPrimeSource

/-!
# Literal quotient-prime sources for the third through sixth Chen terms

For every natural multiplier `b`, the source is the injective image of
original additive primes `P`, with `b ∣ N - P`, under `P ↦ (N - P) / b`.
Its `d`-divisibility fibre is the original prime AP at modulus `b * d`,
minus the actual centre-prime correction. No coprimality between `b` and
`d` is needed for this exact identity, and `b = 0` gives the empty source.

The actual third through sixth Upsilon terms are reindexed as sums of
sifted quotient-source cardinalities. The selectors retain their original
inclusive lower and strict upper endpoints; repeated prime factors in a
receiver are allowed. A quotient equal to one is retained at every cutoff.
Every source has unit weights; different selected factors or pairs remain
different outer summands even if they produce the same quotient value.

This module supplies no analytic estimate and does not assign the generic
quotient source the `b = 1` reciprocal-totient local density. At a prime
already dividing `b`, that assignment would in general be incorrect.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators
open Classical

/-- Original additive-prime labels whose positive receivers are multiples
of the selected multiplier. The centre-coprimality mask is unchanged. -/
def chenQuotientPrimeCarrier (N b : ℕ) : Finset ℕ := by
  classical
  exact (chenAdditivePrimeCarrier N).filter (fun P => b ∣ N - P)

@[simp] theorem mem_chenQuotientPrimeCarrier {N b P : ℕ} :
    P ∈ chenQuotientPrimeCarrier N b ↔
      P ∈ chenAdditivePrimeCarrier N ∧ b ∣ N - P := by
  classical
  simp only [chenQuotientPrimeCarrier, Finset.mem_filter]

/-- The actual quotient receiver source, before imposing roughness. -/
def chenQuotientPrimeSource (N b : ℕ) : Finset ℕ :=
  (chenQuotientPrimeCarrier N b).image (fun P => (N - P) / b)

/-- Division is injective on these exact multiples, including the empty
zero-multiplier carrier. No assumption about squarefreeness is used. -/
theorem chenQuotientPrimeSource_injective {N b P Q : ℕ}
    (hP : P ∈ chenQuotientPrimeCarrier N b)
    (hQ : Q ∈ chenQuotientPrimeCarrier N b)
    (heq : (N - P) / b = (N - Q) / b) : P = Q := by
  obtain ⟨hPc, hPb⟩ := mem_chenQuotientPrimeCarrier.mp hP
  obtain ⟨hQc, hQb⟩ := mem_chenQuotientPrimeCarrier.mp hQ
  apply chenPrimeReceiverSource_shift_injective hPc hQc
  calc
    N - P = b * ((N - P) / b) := (Nat.mul_div_cancel' hPb).symm
    _ = b * ((N - Q) / b) := by rw [heq]
    _ = N - Q := Nat.mul_div_cancel' hQb

/-- Every quotient is positive and retains coprimality to the centre. -/
theorem chenQuotientPrimeSource_data {N b q : ℕ}
    (hq : q ∈ chenQuotientPrimeSource N b) :
    0 < q ∧ q ≤ N ∧ Nat.Coprime q N := by
  obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨hPc, hPb⟩ := mem_chenQuotientPrimeCarrier.mp hP
  obtain ⟨hPN, _, hcop⟩ := mem_chenAdditivePrimeCarrier.mp hPc
  have hmul : b * ((N - P) / b) = N - P := Nat.mul_div_cancel' hPb
  have hpos : 0 < (N - P) / b := by
    by_contra hnot
    have hz : (N - P) / b = 0 := by omega
    rw [hz, mul_zero] at hmul
    omega
  have hdiv : (N - P) / b ∣ N - P := by
    calc
      (N - P) / b ∣ b * ((N - P) / b) := dvd_mul_left _ _
      _ = N - P := hmul
  exact ⟨hpos, (Nat.div_le_self (N - P) b).trans (Nat.sub_le N P),
    ((Nat.coprime_self_sub_left hPN.le).mpr hcop).of_dvd_left hdiv⟩

@[simp] theorem chenQuotientPrimeSource_zero_multiplier (N : ℕ) :
    chenQuotientPrimeSource N 0 = ∅ := by
  classical
  have hc : chenQuotientPrimeCarrier N 0 = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro P hP
    obtain ⟨hPc, hd⟩ := mem_chenQuotientPrimeCarrier.mp hP
    have hPN := (mem_chenAdditivePrimeCarrier.mp hPc).1
    have hz : N - P = 0 := by simpa using hd
    omega
  simp [chenQuotientPrimeSource, hc]

/-- Cardinality after any quotient predicate is exactly cardinality in
original prime labels. This keeps each prime once inside each fibre. -/
theorem chenQuotientPrimeSource_filter_card (N b : ℕ) (r : ℕ → Prop)
    [DecidablePred r] :
    ((chenQuotientPrimeSource N b).filter r).card =
      ((chenAdditivePrimeCarrier N).filter
        (fun P => b ∣ N - P ∧ r ((N - P) / b))).card := by
  classical
  have himage : (chenQuotientPrimeSource N b).filter r =
      ((chenAdditivePrimeCarrier N).filter
        (fun P => b ∣ N - P ∧ r ((N - P) / b))).image
          (fun P => (N - P) / b) := by
    ext q
    constructor
    · intro hq
      obtain ⟨hq, hr⟩ := Finset.mem_filter.mp hq
      obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨hPc, hPb⟩ := mem_chenQuotientPrimeCarrier.mp hP
      exact Finset.mem_image.mpr
        ⟨P, Finset.mem_filter.mpr ⟨hPc, hPb, hr⟩, rfl⟩
    · intro hq
      obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨hPc, hPb, hr⟩ := Finset.mem_filter.mp hP
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr
          ⟨P, mem_chenQuotientPrimeCarrier.mpr ⟨hPc, hPb⟩, rfl⟩, hr⟩
  rw [himage]
  apply Finset.card_image_of_injOn
  intro P hP Q hQ heq
  obtain ⟨hPc, hPb, _⟩ := Finset.mem_filter.mp hP
  obtain ⟨hQc, hQb, _⟩ := Finset.mem_filter.mp hQ
  exact chenQuotientPrimeSource_injective
    (mem_chenQuotientPrimeCarrier.mpr ⟨hPc, hPb⟩)
    (mem_chenQuotientPrimeCarrier.mpr ⟨hQc, hQb⟩) heq

/-- Exact multiplication of the two divisibility conditions. The modulus
is `b * d`, even when `b` and `d` share primes; it is not their lcm. -/
theorem chen_quotient_divisibility_iff (n b d : ℕ) :
    (b ∣ n ∧ d ∣ n / b) ↔ b * d ∣ n := by
  by_cases hb : b = 0
  · subst b
    simp
  have hbpos : 0 < b := Nat.pos_of_ne_zero hb
  constructor
  · rintro ⟨hbn, hd⟩
    have h := mul_dvd_mul (dvd_refl b) hd
    simpa only [Nat.mul_div_cancel' hbn] using h
  · intro hbd
    have hbn : b ∣ n := (dvd_mul_right b d).trans hbd
    refine ⟨hbn, ?_⟩
    obtain ⟨k, hk⟩ := hbd
    refine ⟨k, ?_⟩
    apply Nat.eq_of_mul_eq_mul_left hbpos
    calc
      b * (n / b) = n := Nat.mul_div_cancel' hbn
      _ = (b * d) * k := hk
      _ = b * (d * k) := Nat.mul_assoc b d k

/-- Every divisibility fibre is a literal inclusive prime AP, with the
unchanged centre-prime subtraction. Both zero and unit moduli are covered. -/
theorem chenQuotientPrimeSource_divisibility_fibre_card (N b d : ℕ) :
    (((chenQuotientPrimeSource N b).filter (fun q => d ∣ q)).card : ℝ) =
      chenPrimeAPCount N N (b * d) - chenCentrePrimeAPCount N N (b * d) := by
  classical
  rw [chenQuotientPrimeSource_filter_card]
  have hf : (chenAdditivePrimeCarrier N).filter
      (fun P => b ∣ N - P ∧ d ∣ (N - P) / b) =
      (chenAdditivePrimeCarrier N).filter (fun P => b * d ∣ N - P) := by
    ext P
    simp only [Finset.mem_filter, chen_quotient_divisibility_iff]
  rw [hf, chenAdditivePrimeCarrier_filter_dvd_eq_AP,
    chenAdditivePrimeCarrier_AP_count]

/-- The total source mass is the same formula at quotient modulus one. -/
theorem chenQuotientPrimeSource_card_cast (N b : ℕ) :
    ((chenQuotientPrimeSource N b).card : ℝ) =
      chenPrimeAPCount N N b - chenCentrePrimeAPCount N N b := by
  simpa using chenQuotientPrimeSource_divisibility_fibre_card N b 1

/-- Sifting retains prime divisors equal to the real cutoff. -/
def chenSiftedQuotientPrimeSource (N b : ℕ) (z : ℝ) : Finset ℕ := by
  classical
  exact (chenQuotientPrimeSource N b).filter (ChenPrimeRough z)

/-- The same exact source can be sifted with the ordinary strict prime
product; coprimality to the centre follows from its actual construction. -/
theorem chenSiftedQuotientPrimeSource_eq_coprime_filter (N b : ℕ) (z : ℝ) :
    chenSiftedQuotientPrimeSource N b z =
      (chenQuotientPrimeSource N b).filter
        (fun q => Nat.Coprime q (sieveProduct N (Nat.ceil z))) := by
  classical
  ext q
  simp only [chenSiftedQuotientPrimeSource, Finset.mem_filter]
  constructor
  · rintro ⟨hq, hr⟩
    exact ⟨hq, (chenPrimeRough_iff_coprime_sieveProduct z
      (chenQuotientPrimeSource_data hq).2.2).mp hr⟩
  · rintro ⟨hq, hr⟩
    exact ⟨hq, (chenPrimeRough_iff_coprime_sieveProduct z
      (chenQuotientPrimeSource_data hq).2.2).mpr hr⟩

@[simp] theorem one_mem_chenSiftedQuotientPrimeSource_iff (N b : ℕ) (z : ℝ) :
    1 ∈ chenSiftedQuotientPrimeSource N b z ↔
      1 ∈ chenQuotientPrimeSource N b := by
  classical
  simp [chenSiftedQuotientPrimeSource]

/-- Literal quotient roughness in original additive-prime labels. -/
theorem chenSiftedQuotientPrimeSource_card (N b : ℕ) (z : ℝ) :
    (chenSiftedQuotientPrimeSource N b z).card =
      ((chenAdditivePrimeCarrier N).filter
        (fun P => ChenQuotient b z (N - P))).card := by
  classical
  exact chenQuotientPrimeSource_filter_card N b (ChenPrimeRough z)

/-- Finite Fubini for selected multipliers. The outer tuple label is never
erased, so equal quotient values in different fibres keep multiplicity. -/
theorem chen_sum_quotient_tuple_card {α : Type*} [DecidableEq α]
    (N : ℕ) (T : Finset α) (b : α → ℕ) (z : ℝ) :
    (∑ P ∈ chenAdditivePrimeCarrier N,
      ((T.filter (fun t => ChenQuotient (b t) z (N - P))).card : ℝ)) =
      ∑ t ∈ T, ((chenSiftedQuotientPrimeSource N (b t) z).card : ℝ) := by
  classical
  simp_rw [chenSiftedQuotientPrimeSource_card]
  simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, Finset.sum_filter]
  exact Finset.sum_comm

/-- A prime dividing an actual receiver is itself a primitive additive
prime label below `N`; this proves the outer carrier restriction exactly. -/
private theorem chen_prime_factor_mem_additive_carrier {N P p : ℕ}
    (hP : P ∈ chenAdditivePrimeCarrier N) (hp : Nat.Prime p)
    (hd : p ∣ N - P) : p ∈ chenAdditivePrimeCarrier N := by
  obtain ⟨hPN, hprime, hcop⟩ := mem_chenAdditivePrimeCarrier.mp hP
  have hpos : 0 < N - P := by omega
  have hle : p ≤ N - P := Nat.le_of_dvd hpos hd
  have hPpos := hprime.pos
  exact mem_chenAdditivePrimeCarrier.mpr ⟨by omega, hp,
    ((Nat.coprime_self_sub_left hPN.le).mpr hcop).of_dvd_left hd⟩

/-- The full actual one-prime selector. A lower equality is included, and
an upper equality is excluded, for arbitrary real endpoints. -/
def chenSinglePrimeSelector (N : ℕ) (A U : ℝ) : Finset ℕ := by
  classical
  exact (chenAdditivePrimeCarrier N).filter (fun p => A ≤ (p : ℝ) ∧ (p : ℝ) < U)

/-- The ordered pair selector for the fifth term. -/
def chenY5PrimeSelector (N : ℕ) (A H : ℝ) : Finset (ℕ × ℕ) := by
  classical
  exact (chenAdditivePrimeCarrier N ×ˢ chenAdditivePrimeCarrier N).filter
    (fun t => A ≤ (t.1 : ℝ) ∧ t.1 < t.2 ∧ (t.2 : ℝ) < H)

/-- The sixth selector retains the full second-prime band `[H,D)`. -/
def chenY6PrimeSelector (N : ℕ) (A H D : ℝ) : Finset (ℕ × ℕ) := by
  classical
  exact (chenAdditivePrimeCarrier N ×ˢ chenAdditivePrimeCarrier N).filter
    (fun t => A ≤ (t.1 : ℝ) ∧ (t.1 : ℝ) < H ∧
      H ≤ (t.2 : ℝ) ∧ (t.2 : ℝ) < D)

/-- Remove only the receiver-dependent carrier restriction; every actual
one-factor tuple remains, including repeated occurrences in the receiver. -/
theorem chenSinglePrimeTuples_eq_selector_filter {N P : ℕ}
    (hP : P ∈ chenAdditivePrimeCarrier N) (A U : ℝ) :
    chenSinglePrimeTuples (N - P) A U =
      (chenSinglePrimeSelector N A U).filter
        (fun p => ChenQuotient p A (N - P)) := by
  classical
  have hn : N - P ≠ 0 := by
    have hPN := (mem_chenAdditivePrimeCarrier.mp hP).1
    omega
  ext p
  rw [mem_chenSinglePrimeTuples_iff hn]
  simp only [chenSinglePrimeSelector, Finset.mem_filter]
  constructor
  · rintro ⟨hp, hA, hU, hQ⟩
    exact ⟨⟨chen_prime_factor_mem_additive_carrier hP hp hQ.1, hA, hU⟩, hQ⟩
  · rintro ⟨⟨hp, hA, hU⟩, hQ⟩
    exact ⟨(mem_chenAdditivePrimeCarrier.mp hp).2.1, hA, hU, hQ⟩

/-- Exact pair carrier for the fifth term; no product or quotient image
collapses distinct selected pairs. -/
theorem chenY5Tuples_eq_selector_filter {N P : ℕ}
    (hP : P ∈ chenAdditivePrimeCarrier N) (A H : ℝ) :
    chenY5Tuples (N - P) A H =
      (chenY5PrimeSelector N A H).filter
        (fun t => ChenQuotient (t.1 * t.2) A (N - P)) := by
  classical
  have hn : N - P ≠ 0 := by
    have hPN := (mem_chenAdditivePrimeCarrier.mp hP).1
    omega
  ext t
  rcases t with ⟨p₁, p₂⟩
  rw [mem_chenY5Tuples_iff hn]
  simp only [chenY5PrimeSelector, Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨hp₁, hp₂, hA, h₁₂, hH, hQ⟩
    have h₁ := chen_prime_factor_mem_additive_carrier hP hp₁
      ((dvd_mul_right p₁ p₂).trans hQ.1)
    have h₂ := chen_prime_factor_mem_additive_carrier hP hp₂
      ((dvd_mul_left p₂ p₁).trans hQ.1)
    exact ⟨⟨⟨h₁, h₂⟩, hA, h₁₂, hH⟩, hQ⟩
  · rintro ⟨⟨⟨h₁, h₂⟩, hA, h₁₂, hH⟩, hQ⟩
    exact ⟨(mem_chenAdditivePrimeCarrier.mp h₁).2.1,
      (mem_chenAdditivePrimeCarrier.mp h₂).2.1, hA, h₁₂, hH, hQ⟩

/-- Exact pair carrier for the sixth term, including equality at `H`. -/
theorem chenY6Tuples_eq_selector_filter {N P : ℕ}
    (hP : P ∈ chenAdditivePrimeCarrier N) (A H D : ℝ) :
    chenY6Tuples (N - P) A H D =
      (chenY6PrimeSelector N A H D).filter
        (fun t => ChenQuotient (t.1 * t.2) A (N - P)) := by
  classical
  have hn : N - P ≠ 0 := by
    have hPN := (mem_chenAdditivePrimeCarrier.mp hP).1
    omega
  ext t
  rcases t with ⟨p₁, p₂⟩
  rw [mem_chenY6Tuples_iff hn]
  simp only [chenY6PrimeSelector, Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨hp₁, hp₂, hA, h₁H, hH₂, h₂D, hQ⟩
    have h₁ := chen_prime_factor_mem_additive_carrier hP hp₁
      ((dvd_mul_right p₁ p₂).trans hQ.1)
    have h₂ := chen_prime_factor_mem_additive_carrier hP hp₂
      ((dvd_mul_left p₂ p₁).trans hQ.1)
    exact ⟨⟨⟨h₁, h₂⟩, hA, h₁H, hH₂, h₂D⟩, hQ⟩
  · rintro ⟨⟨⟨h₁, h₂⟩, hA, h₁H, hH₂, h₂D⟩, hQ⟩
    exact ⟨(mem_chenAdditivePrimeCarrier.mp h₁).2.1,
      (mem_chenAdditivePrimeCarrier.mp h₂).2.1, hA, h₁H, hH₂, h₂D, hQ⟩

/-- Both one-prime terms use this exact reindexing at their own upper cap. -/
theorem sum_chenY3_eq_siftedQuotientPrimeSource (N : ℕ) (A U : ℝ) :
    (∑ P ∈ chenAdditivePrimeCarrier N, (chenY3 (N - P) A U : ℝ)) =
      ∑ p ∈ chenSinglePrimeSelector N A U,
        ((chenSiftedQuotientPrimeSource N p A).card : ℝ) := by
  calc
    _ = ∑ P ∈ chenAdditivePrimeCarrier N,
        (((chenSinglePrimeSelector N A U).filter
          (fun p => ChenQuotient p A (N - P))).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro P hP
      rw [chenY3, chenSinglePrimeTuples_eq_selector_filter hP A U]
    _ = _ := chen_sum_quotient_tuple_card N (chenSinglePrimeSelector N A U) id A

/-- The fifth term retains ordered pairs as outer labels. -/
theorem sum_chenY5_eq_siftedQuotientPrimeSource (N : ℕ) (A H : ℝ) :
    (∑ P ∈ chenAdditivePrimeCarrier N, (chenY5 (N - P) A H : ℝ)) =
      ∑ t ∈ chenY5PrimeSelector N A H,
        ((chenSiftedQuotientPrimeSource N (t.1 * t.2) A).card : ℝ) := by
  calc
    _ = ∑ P ∈ chenAdditivePrimeCarrier N,
        (((chenY5PrimeSelector N A H).filter
          (fun t => ChenQuotient (t.1 * t.2) A (N - P))).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro P hP
      rw [chenY5, chenY5Tuples_eq_selector_filter hP A H]
    _ = _ := chen_sum_quotient_tuple_card N (chenY5PrimeSelector N A H)
      (fun t => t.1 * t.2) A

/-- The sixth term keeps the literal half-open second-prime band. -/
theorem sum_chenY6_eq_siftedQuotientPrimeSource (N : ℕ) (A H D : ℝ) :
    (∑ P ∈ chenAdditivePrimeCarrier N, (chenY6 (N - P) A H D : ℝ)) =
      ∑ t ∈ chenY6PrimeSelector N A H D,
        ((chenSiftedQuotientPrimeSource N (t.1 * t.2) A).card : ℝ) := by
  calc
    _ = ∑ P ∈ chenAdditivePrimeCarrier N,
        (((chenY6PrimeSelector N A H D).filter
          (fun t => ChenQuotient (t.1 * t.2) A (N - P))).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro P hP
      rw [chenY6, chenY6Tuples_eq_selector_filter hP A H D]
    _ = _ := chen_sum_quotient_tuple_card N (chenY6PrimeSelector N A H D)
      (fun t => t.1 * t.2) A

/-- Actual Upsilon 3, with the manuscript's strict cubic-root upper cap. -/
theorem chenUpsilon3_eq_siftedQuotientPrimeSource (N : ℕ) :
    chenUpsilon3 N =
      ∑ p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ))
          ((N : ℝ) ^ (1 / 3 : ℝ)),
        ((chenSiftedQuotientPrimeSource N p
          ((N : ℝ) ^ (100 / 1149 : ℝ))).card : ℝ) := by
  exact sum_chenY3_eq_siftedQuotientPrimeSource N _ _

/-- Actual Upsilon 4, at its distinct full upper endpoint. -/
theorem chenUpsilon4_eq_siftedQuotientPrimeSource (N : ℕ) :
    chenUpsilon4 N =
      ∑ p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ))
          ((N : ℝ) ^ ((1 / 2 : ℝ) - 3 * (100 / 1149 : ℝ))),
        ((chenSiftedQuotientPrimeSource N p
          ((N : ℝ) ^ (100 / 1149 : ℝ))).card : ℝ) := by
  exact sum_chenY3_eq_siftedQuotientPrimeSource N _ _

/-- Actual Upsilon 5, preserving strict pair ordering. -/
theorem chenUpsilon5_eq_siftedQuotientPrimeSource (N : ℕ) :
    chenUpsilon5 N =
      ∑ t ∈ chenY5PrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ))
          ((N : ℝ) ^ (50 / 309 : ℝ)),
        ((chenSiftedQuotientPrimeSource N (t.1 * t.2)
          ((N : ℝ) ^ (100 / 1149 : ℝ))).card : ℝ) := by
  exact sum_chenY5_eq_siftedQuotientPrimeSource N _ _

/-- Actual Upsilon 6, with its inclusive lower second-prime endpoint. -/
theorem chenUpsilon6_eq_siftedQuotientPrimeSource (N : ℕ) :
    chenUpsilon6 N =
      ∑ t ∈ chenY6PrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ))
          ((N : ℝ) ^ (50 / 309 : ℝ))
          ((N : ℝ) ^ ((1 / 2 : ℝ) - 3 * (100 / 1149 : ℝ))),
        ((chenSiftedQuotientPrimeSource N (t.1 * t.2)
          ((N : ℝ) ^ (100 / 1149 : ℝ))).card : ℝ) := by
  exact sum_chenY6_eq_siftedQuotientPrimeSource N _ _ _

end

end ImbalancedChen
