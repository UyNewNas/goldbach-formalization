import ImbalancedChen.P5U7ActualFullSourceAsymptotic

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT.
Exact actual cofactor partition. Only the terminal ordered pair is mapped
onto its product; its factorization is unique even on the repeated-prime
wall. The outer pair remains marked throughout. No rough-count endpoint,
target exclusion, or unit correction is silently inserted or removed.
-/

namespace ImbalancedChen

noncomputable section
open scoped BigOperators
open Classical

/-- Actual ordered semiprime cofactors, including r=s. -/
def p5U7ComponentSemiprimeCofactors (N : ℕ) (t : ℕ × ℕ) : Finset ℕ :=
  (p5U7MassSemiprimePairs N t).image (fun u => u.1 * u.2)

/-- Actual cofactor carrier with its prime and ordered-semiprime branches. -/
def p5U7ComponentCofactors (N : ℕ) (t : ℕ × ℕ) : Finset ℕ :=
  p5U7MassPrimeFibre N (t.1 * t.2) t.2 ∪ p5U7ComponentSemiprimeCofactors N t

theorem p5U7ComponentSemiprime_product_injOn (N : ℕ) (t : ℕ × ℕ) :
    Set.InjOn (fun u : ℕ × ℕ => u.1 * u.2) (p5U7MassSemiprimePairs N t) := by
  intro a ha b hb heq
  obtain ⟨hac, _, hoa, _⟩ := Finset.mem_filter.mp ha
  obtain ⟨hbc, _, hob, _⟩ := Finset.mem_filter.mp hb
  obtain ⟨ha1, ha2⟩ := Finset.mem_product.mp hac
  obtain ⟨hb1, hb2⟩ := Finset.mem_product.mp hbc
  obtain ⟨he1, he2⟩ := ordered_prime_factors_unique
    (mem_chenAdditivePrimeCarrier.mp ha1).2.1 (mem_chenAdditivePrimeCarrier.mp ha2).2.1
    (mem_chenAdditivePrimeCarrier.mp hb1).2.1 (mem_chenAdditivePrimeCarrier.mp hb2).2.1
    hoa hob heq
  exact Prod.ext he1 he2

theorem p5U7ComponentSemiprime_not_prime {N : ℕ} {t : ℕ × ℕ} {q : ℕ}
    (hq : q ∈ p5U7ComponentSemiprimeCofactors N t) : ¬ Nat.Prime q := by
  obtain ⟨⟨r, s⟩, hrs, rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨hr, hs⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hrs).1
  exact Nat.not_prime_mul (mem_chenAdditivePrimeCarrier.mp hr).2.1.ne_one
    (mem_chenAdditivePrimeCarrier.mp hs).2.1.ne_one

theorem p5U7ComponentCofactors_disjoint (N : ℕ) (t : ℕ × ℕ) :
    Disjoint (p5U7MassPrimeFibre N (t.1 * t.2) t.2)
      (p5U7ComponentSemiprimeCofactors N t) := by
  apply Finset.disjoint_left.mpr
  intro q hp hs
  exact p5U7ComponentSemiprime_not_prime hs
    (mem_chenAdditivePrimeCarrier.mp (Finset.mem_filter.mp hp).1).2.1

/-- Primality cuts out precisely the actual target-excluding prime window. -/
theorem p5U7ComponentCofactors_filter_prime (N : ℕ) (t : ℕ × ℕ) :
    (p5U7ComponentCofactors N t).filter Nat.Prime =
      p5U7MassPrimeFibre N (t.1 * t.2) t.2 := by
  ext q
  constructor
  · intro hq
    obtain ⟨hq, hp⟩ := Finset.mem_filter.mp hq
    rcases Finset.mem_union.mp hq with hq | hq
    · exact hq
    · exact False.elim (p5U7ComponentSemiprime_not_prime hq hp)
  · intro hq
    exact Finset.mem_filter.mpr ⟨Finset.mem_union_left _ hq,
      (mem_chenAdditivePrimeCarrier.mp (Finset.mem_filter.mp hq).1).2.1⟩

/-- The complementary filter retains all ordered semiprime cofactors. -/
theorem p5U7ComponentCofactors_filter_not_prime (N : ℕ) (t : ℕ × ℕ) :
    (p5U7ComponentCofactors N t).filter (fun q => ¬ Nat.Prime q) =
      p5U7ComponentSemiprimeCofactors N t := by
  ext q
  constructor
  · intro hq
    obtain ⟨hq, hp⟩ := Finset.mem_filter.mp hq
    rcases Finset.mem_union.mp hq with hq | hq
    · exact False.elim (hp
        (mem_chenAdditivePrimeCarrier.mp (Finset.mem_filter.mp hq).1).2.1)
    · exact hq
  · intro hq
    exact Finset.mem_filter.mpr ⟨Finset.mem_union_right _ hq,
      p5U7ComponentSemiprime_not_prime hq⟩

/-- Exact arithmetic row identity, with no half-factor for ordered pairs. -/
theorem p5U7ComponentCofactors_card (N : ℕ) (t : ℕ × ℕ) :
    (p5U7ComponentCofactors N t).card =
      (p5U7MassPrimeFibre N (t.1 * t.2) t.2).card +
        (p5U7MassSemiprimePairs N t).card := by
  rw [p5U7ComponentCofactors, Finset.card_union_of_disjoint
    (p5U7ComponentCofactors_disjoint N t), p5U7ComponentSemiprimeCofactors,
    Finset.card_image_of_injOn (p5U7ComponentSemiprime_product_injOn N t)]

/-- The actual source in the common marked (outer pair, cofactor) space. -/
def p5U7MarkedComponentSource (N : ℕ) : Finset (Σ _ : ℕ × ℕ, ℕ) :=
  (chenY7PrimeSelector N ((N : ℝ) ^ (59 / 250 : ℝ))).sigma
    (p5U7ComponentCofactors N)

/-- In this common carrier the prime component is literally the old
three-label source, rather than an unrelated prime density. -/
theorem p5U7MarkedComponentSource_filter_prime (N : ℕ) :
    (p5U7MarkedComponentSource N).filter (fun x => Nat.Prime x.2) =
      p5U7ArithmeticThree N := by
  ext x
  simp only [p5U7MarkedComponentSource, p5U7ArithmeticThree,
    Finset.mem_filter, Finset.mem_sigma]
  have h := congrArg (fun S : Finset ℕ => x.2 ∈ S)
    (p5U7ComponentCofactors_filter_prime N x.1)
  simp only [Finset.mem_filter] at h
  change (x.1 ∈ _ ∧ x.2 ∈ p5U7ComponentCofactors N x.1) ∧ Nat.Prime x.2 ↔ _
  rw [and_assoc, h]
  rfl

/-- Exact global marked count. Outer product collisions remain separate. -/
theorem p5U7MarkedComponentSource_card (N : ℕ) :
    ((p5U7MarkedComponentSource N).card : ℝ) = p5U7ActualFullSourceMass N := by
  simp only [p5U7MarkedComponentSource, Finset.card_sigma,
    p5U7ComponentCofactors_card, Finset.sum_add_distrib, Nat.cast_add, Nat.cast_sum]
  unfold p5U7ActualFullSourceMass
  rw [p5U7Mass_three_card_eq_primeFibres]
  change _ = _ + (((_).sigma (p5U7MassSemiprimePairs N)).card : ℝ)
  simp only [Finset.card_sigma, Nat.cast_sum]

/-- The separate ordered-semiprime count is obtained by subtracting the
correct actual prime carrier from the full marked cofactor count. -/
theorem p5U7MarkedComponentSource_semiprime_card (N : ℕ) :
    (((p5U7MarkedComponentSource N).filter (fun x => ¬ Nat.Prime x.2)).card : ℝ) =
      ((p5U7ArithmeticFour N).card : ℝ) := by
  have hcard := Finset.card_filter_add_card_filter_not
    (s := p5U7MarkedComponentSource N) (p := fun x => Nat.Prime x.2)
  rw [p5U7MarkedComponentSource_filter_prime] at hcard
  have hcast : ((p5U7ArithmeticThree N).card : ℝ) +
      (((p5U7MarkedComponentSource N).filter (fun x => ¬ Nat.Prime x.2)).card : ℝ) =
      ((p5U7MarkedComponentSource N).card : ℝ) := by exact_mod_cast hcard
  rw [p5U7MarkedComponentSource_card, p5U7ActualFullSourceMass] at hcast
  linarith only [hcast]

end
end ImbalancedChen
