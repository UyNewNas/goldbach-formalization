import ImbalancedChen.CurrentChenMeanLedger
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# The actual ninth source consists of prime and unit quotient fibres

The cutoff is the original `sqrt (N / (p₁ * p₂))`.  An actual additive
prime witness gives `p₁ * p₂ * q = N - P < N`; thus a composite quotient's
least prime factor lies strictly below that cutoff.  No squarefreeness
assumption or supplied factorization is used.

The final equality retains every outer pair label.  The unit fibres are
kept exactly, with no asymptotic estimate asserted in this module.
-/

namespace ImbalancedChen

open scoped BigOperators
open Classical

noncomputable section

/-- An actual quotient witness pays both the strict receiver bound and
the real quotient bound.  The original additive prime label is retained. -/
theorem currentChenUpsilon9_quotient_witness {N b q : ℕ} (hb : 0 < b)
    (hq : q ∈ chenQuotientPrimeSource N b) :
    ∃ P ∈ chenAdditivePrimeCarrier N,
      b * q = N - P ∧ b * q < N ∧ 0 < q ∧
        (q : ℝ) < (N : ℝ) / (b : ℝ) := by
  obtain ⟨P, hP, heq⟩ := Finset.mem_image.mp hq
  obtain ⟨hPc, hd⟩ := mem_chenQuotientPrimeCarrier.mp hP
  obtain ⟨hPN, hprime, _⟩ := mem_chenAdditivePrimeCarrier.mp hPc
  have hmul : b * q = N - P := by
    rw [← heq]
    exact Nat.mul_div_cancel' hd
  have hlt : b * q < N := by
    have hPpos := hprime.pos
    omega
  have hqpos : 0 < q := (chenQuotientPrimeSource_data hq).1
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hltR : (b : ℝ) * (q : ℝ) < (N : ℝ) := by exact_mod_cast hlt
  refine ⟨P, hPc, hmul, hlt, hqpos, ?_⟩
  apply (lt_div_iff₀ hbR).mpr
  simpa only [mul_comm] using hltR

/-- Sifting the actual quotient source at its ninth square-root cutoff
leaves only one and primes.  Repeated factors in the receiver are allowed. -/
theorem currentChenUpsilon9_sqrt_quotient_prime_or_one {N b q : ℕ}
    (hb : 0 < b)
    (hq : q ∈ chenSiftedQuotientPrimeSource N b
      (Real.sqrt ((N : ℝ) / (b : ℝ)))) :
    q = 1 ∨ Nat.Prime q := by
  obtain ⟨hqsource, hrough⟩ := Finset.mem_filter.mp hq
  obtain ⟨P, hP, hmul, hlt, hqpos, hquot⟩ :=
    currentChenUpsilon9_quotient_witness hb hqsource
  by_cases hqone : q = 1
  · exact Or.inl hqone
  right
  by_contra hnotprime
  have hminprime : Nat.Prime (Nat.minFac q) := Nat.minFac_prime hqone
  have hcut := hrough (Nat.minFac q) hminprime (Nat.minFac_dvd q)
  have hminsq : ((Nat.minFac q : ℕ) : ℝ) ^ 2 ≤ (q : ℝ) := by
    exact_mod_cast Nat.minFac_sq_le_self hqpos hnotprime
  have hsqrough : (Real.sqrt ((N : ℝ) / (b : ℝ))) ^ 2 ≤
      ((Nat.minFac q : ℕ) : ℝ) ^ 2 :=
    (sq_le_sq₀ (Real.sqrt_nonneg _) (Nat.cast_nonneg _)).mpr hcut
  have hroot := Real.sq_sqrt
    (div_nonneg (Nat.cast_nonneg N) (Nat.cast_nonneg b))
  nlinarith only [hminsq, hsqrough, hroot, hquot]

/-- The prime-or-unit conclusion for the literal ninth selector and its
product-dependent cutoff.  Its hypotheses are only actual memberships. -/
theorem currentChenUpsilon9_quotient_prime_or_one {N : ℕ} {t : ℕ × ℕ}
    (ht : t ∈ chenY9PrimeSelector N ((N : ℝ) ^ (19 / 125 : ℝ))
      ((N : ℝ) ^ (59 / 250 : ℝ))) {q : ℕ}
    (hq : q ∈ chenSiftedQuotientPrimeSource N (t.1 * t.2)
      (Real.sqrt ((N : ℝ) / ((t.1 : ℝ) * (t.2 : ℝ))))) :
    q = 1 ∨ Nat.Prime q := by
  obtain ⟨htcarrier, _⟩ := Finset.mem_filter.mp ht
  obtain ⟨hfirst, hsecond⟩ := Finset.mem_product.mp htcarrier
  have h₁ := (mem_chenAdditivePrimeCarrier.mp hfirst).2.1.pos
  have h₂ := (mem_chenAdditivePrimeCarrier.mp hsecond).2.1.pos
  apply currentChenUpsilon9_sqrt_quotient_prime_or_one (mul_pos h₁ h₂)
  simpa only [Nat.cast_mul] using hq

/-- A prime quotient in a literal actual source is equivalently its
unchanged additive prime `N-b*q`, the strict product bound, and roughness
at that prime.  Neither implication assumes a source factorization. -/
theorem currentChenUpsilon9_prime_mem_iff {N b q : ℕ} (hb : 0 < b)
    (hqprime : Nat.Prime q) (z : ℝ) :
    q ∈ chenSiftedQuotientPrimeSource N b z ↔
      b * q < N ∧ N - b * q ∈ chenAdditivePrimeCarrier N ∧ z ≤ (q : ℝ) := by
  constructor
  · intro hq
    obtain ⟨hqsource, hrough⟩ := Finset.mem_filter.mp hq
    obtain ⟨P, hP, hmul, hlt, _, _⟩ :=
      currentChenUpsilon9_quotient_witness hb hqsource
    have hPN := (mem_chenAdditivePrimeCarrier.mp hP).1
    have hrecover : N - b * q = P := by omega
    refine ⟨hlt, ?_, hrough q hqprime (dvd_refl q)⟩
    simpa only [hrecover] using hP
  · rintro ⟨hlt, hP, hcut⟩
    have hreceiver : N - (N - b * q) = b * q := Nat.sub_sub_self hlt.le
    have hdiv : b ∣ N - (N - b * q) := by
      rw [hreceiver]
      exact dvd_mul_right b q
    have hquot : (N - (N - b * q)) / b = q := by
      rw [hreceiver]
      exact Nat.mul_div_cancel_left q hb
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨N - b * q,
      mem_chenQuotientPrimeCarrier.mpr ⟨hP, hdiv⟩, hquot⟩, ?_⟩
    intro r hr hrd
    have hrq : r = q := (Nat.prime_dvd_prime_iff_eq hr hqprime).mp hrd
    simpa only [hrq] using hcut

/-- Actual prime triples, with the complete pair as its outer label and
the actual sifted quotient as its third value.  Sigma labels preserve
multiplicity even if different pairs have the same product or quotient. -/
def currentChenUpsilon9PrimeTriples (N : ℕ) : Finset (Σ _ : ℕ × ℕ, ℕ) :=
  (chenY9PrimeSelector N ((N : ℝ) ^ (19 / 125 : ℝ))
    ((N : ℝ) ^ (59 / 250 : ℝ))).sigma fun t =>
      (chenSiftedQuotientPrimeSource N (t.1 * t.2)
        (Real.sqrt ((N : ℝ) / ((t.1 : ℝ) * (t.2 : ℝ))))).filter Nat.Prime

/-- Actual unit fibres of the same ninth source.  No size budget is
silently discarded at this finite arithmetic step. -/
def currentChenUpsilon9UnitFibres (N : ℕ) : Finset (ℕ × ℕ) :=
  (chenY9PrimeSelector N ((N : ℝ) ^ (19 / 125 : ℝ))
    ((N : ℝ) ^ (59 / 250 : ℝ))).filter fun t =>
      1 ∈ chenSiftedQuotientPrimeSource N (t.1 * t.2)
        (Real.sqrt ((N : ℝ) / ((t.1 : ℝ) * (t.2 : ℝ))))

/-- An explicit membership description of the actual prime triples.  It
keeps both original half-open prime ranges, the coupled square-root
cutoff, and the original prime's centre-coprimality condition. -/
theorem mem_currentChenUpsilon9PrimeTriples_iff {N p₁ p₂ q : ℕ} :
    (⟨(p₁, p₂), q⟩ : Σ _ : ℕ × ℕ, ℕ) ∈ currentChenUpsilon9PrimeTriples N ↔
      p₁ ∈ chenAdditivePrimeCarrier N ∧ p₂ ∈ chenAdditivePrimeCarrier N ∧
      (N : ℝ) ^ (19 / 125 : ℝ) ≤ (p₁ : ℝ) ∧
      (p₁ : ℝ) < (N : ℝ) ^ (59 / 250 : ℝ) ∧
      (N : ℝ) ^ (59 / 250 : ℝ) ≤ (p₂ : ℝ) ∧
      (p₂ : ℝ) < Real.sqrt ((N : ℝ) / (p₁ : ℝ)) ∧
      Nat.Prime q ∧ p₁ * p₂ * q < N ∧
      N - p₁ * p₂ * q ∈ chenAdditivePrimeCarrier N ∧
      Real.sqrt ((N : ℝ) / ((p₁ : ℝ) * (p₂ : ℝ))) ≤ (q : ℝ) := by
  simp only [currentChenUpsilon9PrimeTriples, Finset.mem_sigma,
    chenY9PrimeSelector, Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨⟨⟨h₁, h₂⟩, hH, h₁D, hD₂, hcap⟩, hq, hprime⟩
    have hb : 0 < p₁ * p₂ := mul_pos
      (mem_chenAdditivePrimeCarrier.mp h₁).2.1.pos
      (mem_chenAdditivePrimeCarrier.mp h₂).2.1.pos
    obtain ⟨hlt, hP, hcut⟩ := (currentChenUpsilon9_prime_mem_iff hb hprime _).mp hq
    exact ⟨h₁, h₂, hH, h₁D, hD₂, hcap, hprime, hlt, hP, hcut⟩
  · rintro ⟨h₁, h₂, hH, h₁D, hD₂, hcap, hprime, hlt, hP, hcut⟩
    have hb : 0 < p₁ * p₂ := mul_pos
      (mem_chenAdditivePrimeCarrier.mp h₁).2.1.pos
      (mem_chenAdditivePrimeCarrier.mp h₂).2.1.pos
    exact ⟨⟨⟨h₁, h₂⟩, hH, h₁D, hD₂, hcap⟩,
      (currentChenUpsilon9_prime_mem_iff hb hprime _).mpr ⟨hlt, hP, hcut⟩, hprime⟩

/-- Every actual ninth row is exactly the disjoint union of its prime
quotients and its possible unit quotient. -/
theorem currentChenUpsilon9_row_card_partition {N : ℕ} {t : ℕ × ℕ}
    (ht : t ∈ chenY9PrimeSelector N ((N : ℝ) ^ (19 / 125 : ℝ))
      ((N : ℝ) ^ (59 / 250 : ℝ))) :
    let F := chenSiftedQuotientPrimeSource N (t.1 * t.2)
      (Real.sqrt ((N : ℝ) / ((t.1 : ℝ) * (t.2 : ℝ))))
    F.card = (F.filter Nat.Prime).card + if 1 ∈ F then 1 else 0 := by
  intro F
  have hcompl : F.filter (fun q => ¬ Nat.Prime q) =
      if 1 ∈ F then {1} else ∅ := by
    ext q
    by_cases hunit : 1 ∈ F
    · simp only [hunit, if_true, Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hq, hnot⟩
        exact (currentChenUpsilon9_quotient_prime_or_one ht hq).resolve_right hnot
      · rintro rfl
        exact ⟨hunit, Nat.not_prime_one⟩
    · simp only [hunit, if_false, Finset.mem_filter, Finset.notMem_empty, iff_false,
        not_and]
      intro hq hnot
      have hqone := (currentChenUpsilon9_quotient_prime_or_one ht hq).resolve_right hnot
      exact hunit (hqone ▸ hq)
  have hpartition := Finset.card_filter_add_card_filter_not (s := F) Nat.Prime
  rw [hcompl] at hpartition
  by_cases hunit : 1 ∈ F <;> simpa only [hunit, if_true, if_false,
    Finset.card_singleton, Finset.card_empty] using hpartition.symm

/-- Exact reindexing of the current ninth count into actual prime triples
and the actual unit fibres.  No pair labels, endpoint ownership, original
prime coprimality, or moving quotient cutoff are lost. -/
theorem currentChenUpsilon9_eq_primeTriples_add_unitFibres (N : ℕ) :
    currentChenUpsilon9 N =
      ((currentChenUpsilon9PrimeTriples N).card : ℝ) +
        ((currentChenUpsilon9UnitFibres N).card : ℝ) := by
  rw [currentChenUpsilon9_eq_siftedQuotientPrimeSource]
  have hunitcount : ((currentChenUpsilon9UnitFibres N).card : ℝ) =
      ∑ t ∈ chenY9PrimeSelector N ((N : ℝ) ^ (19 / 125 : ℝ))
        ((N : ℝ) ^ (59 / 250 : ℝ)),
        if 1 ∈ chenSiftedQuotientPrimeSource N (t.1 * t.2)
          (Real.sqrt ((N : ℝ) / ((t.1 : ℝ) * (t.2 : ℝ))))
        then (1 : ℝ) else 0 := by
    simp only [currentChenUpsilon9UnitFibres, Finset.card_eq_sum_ones,
      Finset.sum_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [hunitcount]
  simp only [currentChenUpsilon9PrimeTriples, Finset.card_sigma, Nat.cast_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  exact_mod_cast currentChenUpsilon9_row_card_partition ht

end

end ImbalancedChen
