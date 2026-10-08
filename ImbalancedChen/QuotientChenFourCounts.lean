import ImbalancedChen.QuotientChenFourPrime
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod

/-!
# Exact `Y10` and full `Y11` identities from their actual quotient tuples

This file counts the literal tuple sets defined in `QuotientChenFourPrime`.
For a squarefree receiver whose smallest two factors lie in `[A,H)`, it proves
`Y10 = choose (r - 2) 2` and `Y11 full = (r - 2) * (s - r)`, where `r` and `s`
are the actual numbers of prime divisors strictly below `H` and `D`.

The bridge is an explicit equality of tuple sets with injective images of
ordered tail pairs and a Cartesian product. Thus these are finite source
identities, not scalar identities supplied as assumptions. All endpoints are
literal: the `Y11` fourth-prime band is `[H,D)`, including its lower endpoint.
-/

namespace ImbalancedChen

noncomputable section

def chenPrimesBelow (n : ℕ) (H : ℝ) : Finset ℕ := by
  classical
  exact n.primeFactors.filter fun p => (p : ℝ) < H

def chenPrimeBand (n : ℕ) (H D : ℝ) : Finset ℕ := by
  classical
  exact n.primeFactors.filter fun p => H ≤ (p : ℝ) ∧ (p : ℝ) < D

def chenTailBelow (n q₂ : ℕ) (H : ℝ) : Finset ℕ := by
  classical
  exact n.primeFactors.filter fun p => q₂ < p ∧ (p : ℝ) < H

def chenTailPairs (n q₂ : ℕ) (H : ℝ) : Finset (ℕ × ℕ) :=
  ((chenTailBelow n q₂ H) ×ˢ (chenTailBelow n q₂ H)).filter fun t => t.1 < t.2

/-- Cardinality of the exact nonzero quotient summands of `Y10`. -/
def chenY10 (n : ℕ) (A H : ℝ) : ℕ := (chenY10Tuples n A H).card

/-- Cardinality of the exact nonzero full-range quotient summands of `Y11`. -/
def chenY11Full (n : ℕ) (A H D : ℝ) : ℕ := (chenY11FullTuples n A H D).card

theorem mem_chenPrimesBelow {n p : ℕ} {H : ℝ} (hn : n ≠ 0) :
    p ∈ chenPrimesBelow n H ↔ Nat.Prime p ∧ p ∣ n ∧ (p : ℝ) < H := by
  classical
  rw [chenPrimesBelow, Finset.mem_filter]
  constructor
  · rintro ⟨hp, hH⟩
    obtain ⟨hprime, hdvd, _⟩ := Nat.mem_primeFactors.mp hp
    exact ⟨hprime, hdvd, hH⟩
  · rintro ⟨hprime, hdvd, hH⟩
    exact ⟨Nat.mem_primeFactors.mpr ⟨hprime, hdvd, hn⟩, hH⟩

theorem mem_chenPrimeBand {n p : ℕ} {H D : ℝ} (hn : n ≠ 0) :
    p ∈ chenPrimeBand n H D ↔
      Nat.Prime p ∧ p ∣ n ∧ H ≤ (p : ℝ) ∧ (p : ℝ) < D := by
  classical
  rw [chenPrimeBand, Finset.mem_filter]
  constructor
  · rintro ⟨hp, hH, hD⟩
    obtain ⟨hprime, hdvd, _⟩ := Nat.mem_primeFactors.mp hp
    exact ⟨hprime, hdvd, hH, hD⟩
  · rintro ⟨hprime, hdvd, hH, hD⟩
    exact ⟨Nat.mem_primeFactors.mpr ⟨hprime, hdvd, hn⟩, hH, hD⟩

theorem mem_chenTailBelow {n q₂ p : ℕ} {H : ℝ} (hn : n ≠ 0) :
    p ∈ chenTailBelow n q₂ H ↔
      Nat.Prime p ∧ p ∣ n ∧ q₂ < p ∧ (p : ℝ) < H := by
  classical
  rw [chenTailBelow, Finset.mem_filter]
  constructor
  · rintro ⟨hp, hq₂, hH⟩
    obtain ⟨hprime, hdvd, _⟩ := Nat.mem_primeFactors.mp hp
    exact ⟨hprime, hdvd, hq₂, hH⟩
  · rintro ⟨hprime, hdvd, hq₂, hH⟩
    exact ⟨Nat.mem_primeFactors.mpr ⟨hprime, hdvd, hn⟩, hq₂, hH⟩

/-- Every actual `Y10` tuple has the same first two coordinates, and its
last two coordinates can be chosen freely subject to their strict order. -/
theorem chenY10Tuples_eq_tail_image {n q₁ q₂ : ℕ} {A H : ℝ}
    (hn : Squarefree n) (hsmall : ChenSmallestTwo n q₁ q₂) (hA : A ≤ (q₁ : ℝ)) :
    chenY10Tuples n A H =
      (chenTailPairs n q₂ H).image (fun t : ℕ × ℕ => ((q₁, q₂), t)) := by
  classical
  ext ⟨⟨p₁, p₂⟩, ⟨p₃, p₄⟩⟩
  rw [mem_chenY10Tuples_iff_smallestTwo hn]
  constructor
  · rintro ⟨hp, h₃, h₄, _, h₂₃, h₃₄, h₄H⟩
    obtain ⟨rfl, rfl⟩ := hp.unique hsmall
    have h₃H : (p₃ : ℝ) < H :=
      lt_trans (by exact_mod_cast h₃₄) h₄H
    refine Finset.mem_image.mpr ⟨(p₃, p₄), ?_, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, h₃₄⟩
    · exact (mem_chenTailBelow hn.ne_zero).mpr ⟨h₃.1, h₃.2, h₂₃, h₃H⟩
    · exact (mem_chenTailBelow hn.ne_zero).mpr
        ⟨h₄.1, h₄.2, lt_trans h₂₃ h₃₄, h₄H⟩
  · intro ht
    obtain ⟨⟨u, v⟩, huv, heq⟩ := Finset.mem_image.mp ht
    have heq₁ := congrArg (fun t : (ℕ × ℕ) × (ℕ × ℕ) => t.1.1) heq
    have heq₂ := congrArg (fun t : (ℕ × ℕ) × (ℕ × ℕ) => t.1.2) heq
    have heq₃ := congrArg (fun t : (ℕ × ℕ) × (ℕ × ℕ) => t.2.1) heq
    have heq₄ := congrArg (fun t : (ℕ × ℕ) × (ℕ × ℕ) => t.2.2) heq
    dsimp at heq₁ heq₂ heq₃ heq₄
    subst p₁ p₂ u v
    obtain ⟨hprod, h₃₄⟩ := Finset.mem_filter.mp huv
    obtain ⟨hu, hv⟩ := Finset.mem_product.mp hprod
    obtain ⟨h₃, hd₃, h₂₃, _⟩ := (mem_chenTailBelow hn.ne_zero).mp hu
    obtain ⟨h₄, hd₄, _, h₄H⟩ := (mem_chenTailBelow hn.ne_zero).mp hv
    exact ⟨hsmall, ⟨h₃, hd₃⟩, ⟨h₄, hd₄⟩, hA, h₂₃, h₃₄, h₄H⟩

/-- The full `Y11` source is exactly a Cartesian product of its third-prime
tail and its entire fourth-prime band. -/
theorem chenY11FullTuples_eq_tail_band_image {n q₁ q₂ : ℕ} {A H D : ℝ}
    (hn : Squarefree n) (hsmall : ChenSmallestTwo n q₁ q₂) (hA : A ≤ (q₁ : ℝ)) :
    chenY11FullTuples n A H D =
      ((chenTailBelow n q₂ H) ×ˢ (chenPrimeBand n H D)).image
        (fun t : ℕ × ℕ => ((q₁, q₂), t)) := by
  classical
  ext ⟨⟨p₁, p₂⟩, ⟨p₃, p₄⟩⟩
  rw [mem_chenY11FullTuples_iff_smallestTwo hn]
  constructor
  · rintro ⟨hp, h₃, h₄, _, h₂₃, h₃H, hH₄, h₄D⟩
    obtain ⟨rfl, rfl⟩ := hp.unique hsmall
    refine Finset.mem_image.mpr ⟨(p₃, p₄), Finset.mem_product.mpr ⟨?_, ?_⟩, rfl⟩
    · exact (mem_chenTailBelow hn.ne_zero).mpr ⟨h₃.1, h₃.2, h₂₃, h₃H⟩
    · exact (mem_chenPrimeBand hn.ne_zero).mpr ⟨h₄.1, h₄.2, hH₄, h₄D⟩
  · intro ht
    obtain ⟨⟨u, v⟩, huv, heq⟩ := Finset.mem_image.mp ht
    have heq₁ := congrArg (fun t : (ℕ × ℕ) × (ℕ × ℕ) => t.1.1) heq
    have heq₂ := congrArg (fun t : (ℕ × ℕ) × (ℕ × ℕ) => t.1.2) heq
    have heq₃ := congrArg (fun t : (ℕ × ℕ) × (ℕ × ℕ) => t.2.1) heq
    have heq₄ := congrArg (fun t : (ℕ × ℕ) × (ℕ × ℕ) => t.2.2) heq
    dsimp at heq₁ heq₂ heq₃ heq₄
    subst p₁ p₂ u v
    obtain ⟨hu, hv⟩ := Finset.mem_product.mp huv
    obtain ⟨h₃, hd₃, h₂₃, h₃H⟩ := (mem_chenTailBelow hn.ne_zero).mp hu
    obtain ⟨h₄, hd₄, hH₄, h₄D⟩ := (mem_chenPrimeBand hn.ne_zero).mp hv
    exact ⟨hsmall, ⟨h₃, hd₃⟩, ⟨h₄, hd₄⟩, hA, h₂₃, h₃H, hH₄, h₄D⟩

theorem chenY10_eq_choose_tail {n q₁ q₂ : ℕ} {A H : ℝ}
    (hn : Squarefree n) (hsmall : ChenSmallestTwo n q₁ q₂) (hA : A ≤ (q₁ : ℝ)) :
    chenY10 n A H = (chenTailBelow n q₂ H).card.choose 2 := by
  classical
  unfold chenY10
  rw [chenY10Tuples_eq_tail_image hn hsmall hA]
  rw [Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h)]
  exact Finset.card_product_filter_lt

theorem chenY11Full_eq_tail_mul_band {n q₁ q₂ : ℕ} {A H D : ℝ}
    (hn : Squarefree n) (hsmall : ChenSmallestTwo n q₁ q₂) (hA : A ≤ (q₁ : ℝ)) :
    chenY11Full n A H D = (chenTailBelow n q₂ H).card * (chenPrimeBand n H D).card := by
  classical
  unfold chenY11Full
  rw [chenY11FullTuples_eq_tail_band_image hn hsmall hA]
  rw [Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h)]
  exact Finset.card_product _ _

/-- Removing the actual smallest two prime factors removes exactly two
elements, including when there are no further factors below `H`. -/
theorem chenTailBelow_card {n q₁ q₂ : ℕ} {H : ℝ}
    (hn : n ≠ 0) (hsmall : ChenSmallestTwo n q₁ q₂) (hq₂H : (q₂ : ℝ) < H) :
    (chenTailBelow n q₂ H).card = (chenPrimesBelow n H).card - 2 := by
  classical
  have hq₁H : (q₁ : ℝ) < H :=
    lt_trans (by exact_mod_cast hsmall.increasing) hq₂H
  have hset : chenPrimesBelow n H = insert q₁ (insert q₂ (chenTailBelow n q₂ H)) := by
    ext p
    rw [mem_chenPrimesBelow hn, Finset.mem_insert, Finset.mem_insert, mem_chenTailBelow hn]
    constructor
    · rintro ⟨hp, hdp, hpH⟩
      rcases hsmall.least_other p hp hdp with heq | hle
      · exact Or.inl heq
      · by_cases heq : p = q₂
        · exact Or.inr (Or.inl heq)
        · exact Or.inr (Or.inr ⟨hp, hdp, by omega, hpH⟩)
    · rintro (rfl | rfl | ⟨hp, hdp, _, hpH⟩)
      · exact ⟨hsmall.first_prime, hsmall.first_dvd, hq₁H⟩
      · exact ⟨hsmall.second_prime, hsmall.second_dvd, hq₂H⟩
      · exact ⟨hp, hdp, hpH⟩
  have hnot₂ : q₂ ∉ chenTailBelow n q₂ H := by
    intro h
    exact (lt_irrefl q₂) ((mem_chenTailBelow hn).mp h).2.2.1
  have hnot₁ : q₁ ∉ insert q₂ (chenTailBelow n q₂ H) := by
    intro h
    rcases Finset.mem_insert.mp h with heq | ht
    · exact (ne_of_lt hsmall.increasing) heq
    · exact (not_lt_of_ge (le_of_lt hsmall.increasing)) ((mem_chenTailBelow hn).mp ht).2.2.1
  have hcard : (chenPrimesBelow n H).card = (chenTailBelow n q₂ H).card + 2 := by
    rw [hset, Finset.card_insert_of_notMem hnot₁, Finset.card_insert_of_notMem hnot₂]
    omega
  omega

/-- Exact finite interval subtraction, retaining the lower endpoint `H`. -/
theorem chenPrimeBand_card {n : ℕ} {H D : ℝ} (hn : n ≠ 0) (hHD : H ≤ D) :
    (chenPrimeBand n H D).card = (chenPrimesBelow n D).card - (chenPrimesBelow n H).card := by
  classical
  have hset : chenPrimesBelow n D = chenPrimesBelow n H ∪ chenPrimeBand n H D := by
    ext p
    rw [Finset.mem_union, mem_chenPrimesBelow hn, mem_chenPrimesBelow hn,
      mem_chenPrimeBand hn]
    constructor
    · rintro ⟨hp, hdp, hpD⟩
      by_cases hpH : (p : ℝ) < H
      · exact Or.inl ⟨hp, hdp, hpH⟩
      · exact Or.inr ⟨hp, hdp, le_of_not_gt hpH, hpD⟩
    · rintro (⟨hp, hdp, hpH⟩ | ⟨hp, hdp, _, hpD⟩)
      · exact ⟨hp, hdp, lt_of_lt_of_le hpH hHD⟩
      · exact ⟨hp, hdp, hpD⟩
  have hdisjoint : Disjoint (chenPrimesBelow n H) (chenPrimeBand n H D) := by
    apply Finset.disjoint_left.mpr
    intro p hp hb
    exact (not_lt_of_ge ((mem_chenPrimeBand hn).mp hb).2.2.1)
      ((mem_chenPrimesBelow hn).mp hp).2.2
  have hcard := Finset.card_union_of_disjoint hdisjoint
  rw [← hset] at hcard
  omega

/-- The manuscript's `Y10 = binom(r-2,2)`, proved from the actual quotient
tuples, where `r` counts prime divisors strictly below `H`. -/
theorem chenY10_eq_choose_sub_two {n q₁ q₂ : ℕ} {A H : ℝ}
    (hn : Squarefree n) (hsmall : ChenSmallestTwo n q₁ q₂)
    (hA : A ≤ (q₁ : ℝ)) (hq₂H : (q₂ : ℝ) < H) :
    chenY10 n A H = ((chenPrimesBelow n H).card - 2).choose 2 := by
  rw [chenY10_eq_choose_tail hn hsmall hA, chenTailBelow_card hn.ne_zero hsmall hq₂H]

/-- The manuscript's full-range `Y11 = (r-2)(s-r)`, with `r,s` the literal
strict-cutoff prime-divisor counts. Specialize `A,H,D` to `N^a,N^h,N^d`. -/
theorem chenY11Full_eq_sub_two_mul_sub {n q₁ q₂ : ℕ} {A H D : ℝ}
    (hn : Squarefree n) (hsmall : ChenSmallestTwo n q₁ q₂)
    (hA : A ≤ (q₁ : ℝ)) (hq₂H : (q₂ : ℝ) < H) (hHD : H ≤ D) :
    chenY11Full n A H D = ((chenPrimesBelow n H).card - 2) *
      ((chenPrimesBelow n D).card - (chenPrimesBelow n H).card) := by
  rw [chenY11Full_eq_tail_mul_band hn hsmall hA,
    chenTailBelow_card hn.ne_zero hsmall hq₂H, chenPrimeBand_card hn.ne_zero hHD]

end

end ImbalancedChen
