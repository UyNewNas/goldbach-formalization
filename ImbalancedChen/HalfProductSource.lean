import ImbalancedChen.BadSourceLocalization
import Mathlib.Data.Finset.Prod

/-!
# The finite half-product sieve source

`halfProductSource` is the manuscript's set of integers `m = r * q` with
`T ≤ m ≤ N`, ordered prime factors `r ≤ q`, and strict badness
`q ^ num < r ^ den`. The lower cutoff is real and the upper endpoint is
inclusive. It has no additive-prime condition: that condition is imposed
only by an explicit filter, which is proved to equal `retainedBadReceiversReal`.

Multiplication is a bijection from the finite ordered-pair set to the source.
The bijection remains valid after any predicate on the product is imposed.
There is no factor of two and no removal of prime squares. The source has
the rough factors established in `HalfProductGeometry`.

These are exact finite statements. Neither a prime-counting asymptotic nor
an upper-bound sieve estimate is assumed or proved here.
-/

namespace ImbalancedChen

noncomputable section

/-- The manuscript's half-products, with the literal real lower cutoff and
inclusive upper endpoint. Strict badness is encoded by natural powers. -/
def halfProductSource (num den N : ℕ) (T : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range (N + 1)).filter fun m : ℕ =>
    T ≤ (m : ℝ) ∧ OrderedBadReceiver num den m

@[simp] theorem mem_halfProductSource {num den N m : ℕ} {T : ℝ} :
    m ∈ halfProductSource num den N T ↔
      m ≤ N ∧ T ≤ (m : ℝ) ∧ OrderedBadReceiver num den m := by
  classical
  simp only [halfProductSource, Finset.mem_filter, Finset.mem_range,
    Nat.lt_succ_iff]

/-- Membership in the actual finite source, exposing all factor conditions. -/
theorem mem_halfProductSource_iff_ordered_factors {num den N m : ℕ} {T : ℝ} :
    m ∈ halfProductSource num den N T ↔
      m ≤ N ∧ T ≤ (m : ℝ) ∧
        ∃ r q : ℕ, Nat.Prime r ∧ Nat.Prime q ∧ m = r * q ∧
          r ≤ q ∧ q ^ num < r ^ den :=
  mem_halfProductSource

/-- Exact real-power form of the manuscript's half-product source.
Only this translation needs a positive denominator. -/
theorem mem_halfProductSource_iff_ordered_real_factors
    {num den N m : ℕ} {T : ℝ} (hden : 0 < den) :
    m ∈ halfProductSource num den N T ↔
      m ≤ N ∧ T ≤ (m : ℝ) ∧
        ∃ r q : ℕ, Nat.Prime r ∧ Nat.Prime q ∧ m = r * q ∧ r ≤ q ∧
          (q : ℝ) ^ ((num : ℝ) / (den : ℝ)) < (r : ℝ) := by
  rw [mem_halfProductSource, ← badReceiver_iff_orderedBadReceiver,
    badReceiver_iff_ordered_real_factors hden]

/-- Prime factors ensure positivity even if the lower cutoff is nonpositive. -/
theorem halfProductSource_pos {num den N m : ℕ} {T : ℝ}
    (hm : m ∈ halfProductSource num den N T) : 0 < m := by
  obtain ⟨_, _, r, q, hr, hq, hm, _, _⟩ :=
    mem_halfProductSource_iff_ordered_factors.mp hm
  rw [hm]
  exact Nat.mul_pos hr.pos hq.pos

/-- The retained bad source is exactly the half-products whose additive
partners are prime. The strict upper endpoint is retained explicitly. -/
theorem retainedBadReceiversReal_eq_halfProductSource_filter
    (num den N : ℕ) (T : ℝ) :
    retainedBadReceiversReal num den N T =
      (halfProductSource num den N T).filter
        (fun m => m < N ∧ Nat.Prime (N - m)) := by
  classical
  ext m
  rw [mem_retainedBadReceiversReal, Finset.mem_filter]
  constructor
  · rintro ⟨hmem, hcut⟩
    rcases mem_badReceivers.mp hmem with ⟨hmN, _, hp, hbad⟩
    exact ⟨mem_halfProductSource.mpr
      ⟨hmN.le, hcut, badReceiver_iff_orderedBadReceiver.mp hbad⟩, hmN, hp⟩
  · rintro ⟨hmem, hmN, hp⟩
    rcases mem_halfProductSource.mp hmem with ⟨_, hcut, hbad⟩
    exact ⟨mem_badReceivers.mpr
      ⟨hmN, halfProductSource_pos hmem, hp,
        badReceiver_iff_orderedBadReceiver.mpr hbad⟩, hcut⟩

/-- Every retained bad receiver belongs to the half-product sieve source. -/
theorem retainedBadReceiversReal_subset_halfProductSource
    (num den N : ℕ) (T : ℝ) :
    retainedBadReceiversReal num den N T ⊆ halfProductSource num den N T := by
  classical
  rw [retainedBadReceiversReal_eq_halfProductSource_filter]
  exact Finset.filter_subset _ _

/-- Ordered prime-factor pairs for the half-product source. The finite
ambient square only supplies a bound; the product cutoff is also imposed. -/
def halfProductPairs (num den N : ℕ) (T : ℝ) : Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.range (N + 1)).product (Finset.range (N + 1))).filter fun a : ℕ × ℕ =>
    Nat.Prime a.1 ∧ Nat.Prime a.2 ∧ a.1 ≤ a.2 ∧
      a.2 ^ num < a.1 ^ den ∧ T ≤ (a.1 * a.2 : ℕ) ∧ a.1 * a.2 ≤ N

/-- Primality and the product bound imply the ambient bounds on each factor. -/
@[simp] theorem mem_halfProductPairs {num den N r q : ℕ} {T : ℝ} :
    (r, q) ∈ halfProductPairs num den N T ↔
      Nat.Prime r ∧ Nat.Prime q ∧ r ≤ q ∧ q ^ num < r ^ den ∧
        T ≤ (r * q : ℕ) ∧ r * q ≤ N := by
  classical
  simp only [halfProductPairs, Finset.mem_filter, Finset.mem_product,
    Finset.mem_range, Nat.lt_succ_iff]
  constructor
  · exact fun h => h.2
  · intro h
    have hr1 : 1 ≤ r := le_trans (by decide : 1 ≤ 2) h.1.two_le
    have hq1 : 1 ≤ q := le_trans (by decide : 1 ≤ 2) h.2.1.two_le
    have hrN : r ≤ N := by
      calc
        r = r * 1 := (Nat.mul_one r).symm
        _ ≤ r * q := Nat.mul_le_mul_left r hq1
        _ ≤ N := h.2.2.2.2.2
    have hqN : q ≤ N := by
      calc
        q = 1 * q := (Nat.one_mul q).symm
        _ ≤ r * q := Nat.mul_le_mul_right q hr1
        _ ≤ N := h.2.2.2.2.2
    exact ⟨⟨hrN, hqN⟩, h⟩

/-- Multiplication sends every ordered factor pair into the half-product source. -/
theorem mul_mem_halfProductSource {num den N : ℕ} {T : ℝ} {a : ℕ × ℕ}
    (ha : a ∈ halfProductPairs num den N T) :
    a.1 * a.2 ∈ halfProductSource num den N T := by
  rcases a with ⟨r, q⟩
  rcases mem_halfProductPairs.mp ha with ⟨hr, hq, hrq, hpow, hcut, hN⟩
  exact mem_halfProductSource_iff_ordered_factors.mpr
    ⟨hN, hcut, r, q, hr, hq, rfl, hrq, hpow⟩

/-- Unique ordered factorization makes multiplication injective on the
source pairs, also when either pair is a prime square. -/
theorem halfProductPairs_mul_injective {num den N : ℕ} {T : ℝ}
    {a b : ℕ × ℕ} (ha : a ∈ halfProductPairs num den N T)
    (hb : b ∈ halfProductPairs num den N T) (hmul : a.1 * a.2 = b.1 * b.2) :
    a = b := by
  rcases a with ⟨r, q⟩
  rcases b with ⟨s, t⟩
  rcases mem_halfProductPairs.mp ha with ⟨hr, hq, hrq, _, _, _⟩
  rcases mem_halfProductPairs.mp hb with ⟨hs, ht, hst, _, _, _⟩
  obtain ⟨hrs, hqt⟩ := ordered_prime_factors_unique hr hq hs ht hrq hst hmul
  exact Prod.ext hrs hqt

/-- Every half-product is represented by exactly one ordered pair.
This is uniqueness as a pair, rather than merely existence of two witnesses. -/
theorem halfProductSource_existsUnique_pair {num den N m : ℕ} {T : ℝ}
    (hm : m ∈ halfProductSource num den N T) :
    ∃! a : ℕ × ℕ, a ∈ halfProductPairs num den N T ∧ a.1 * a.2 = m := by
  obtain ⟨hN, hcut, r, q, hr, hq, hm, hrq, hpow⟩ :=
    mem_halfProductSource_iff_ordered_factors.mp hm
  have hp : (r, q) ∈ halfProductPairs num den N T :=
    mem_halfProductPairs.mpr ⟨hr, hq, hrq, hpow, hm ▸ hcut, hm ▸ hN⟩
  refine ⟨(r, q), ⟨hp, hm.symm⟩, ?_⟩
  intro a ha
  exact halfProductPairs_mul_injective ha.1 hp (ha.2.trans hm)

/-- Multiplication realizes the finite half-product set exactly, without
adding partner primality or discarding square endpoints. -/
theorem halfProductPairs_image_mul (num den N : ℕ) (T : ℝ) :
    (halfProductPairs num den N T).image (fun a => a.1 * a.2) =
      halfProductSource num den N T := by
  classical
  ext m
  constructor
  · intro hm
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hm
    exact mul_mem_halfProductSource ha
  · intro hm
    obtain ⟨a, ha, _⟩ := halfProductSource_existsUnique_pair hm
    exact Finset.mem_image.mpr ⟨a, ha.1, ha.2⟩

/-- Ordered-pair counting and integer counting agree exactly, including squares. -/
theorem halfProductPairs_card_eq (num den N : ℕ) (T : ℝ) :
    (halfProductPairs num den N T).card = (halfProductSource num den N T).card := by
  classical
  rw [← halfProductPairs_image_mul]
  symm
  apply Finset.card_image_of_injOn
  intro a ha b hb hab
  exact halfProductPairs_mul_injective ha hb hab

/-- The same exact counting bridge survives every further restriction on
products. In particular it applies to the actual prime-partner sieve filter. -/
theorem halfProductPairs_filter_card_eq (num den N : ℕ) (T : ℝ) (P : ℕ → Prop)
    [DecidablePred P] :
    ((halfProductPairs num den N T).filter (fun a => P (a.1 * a.2))).card =
      ((halfProductSource num den N T).filter P).card := by
  classical
  refine Finset.card_bij (fun a _ => a.1 * a.2) ?_ ?_ ?_
  · intro a ha
    rcases Finset.mem_filter.mp ha with ⟨ha, hP⟩
    exact Finset.mem_filter.mpr ⟨mul_mem_halfProductSource ha, hP⟩
  · intro a ha b hb hab
    exact halfProductPairs_mul_injective (Finset.mem_filter.mp ha).1
      (Finset.mem_filter.mp hb).1 hab
  · intro m hm
    rcases Finset.mem_filter.mp hm with ⟨hm, hP⟩
    obtain ⟨a, ha, _⟩ := halfProductSource_existsUnique_pair hm
    refine ⟨a, Finset.mem_filter.mpr ⟨ha.1, ?_⟩, ha.2⟩
    simpa only [ha.2] using hP

/-- Prime squares satisfy exactly the same cutoff and strict-power tests;
there is no hidden requirement that the two primes be distinct. -/
theorem prime_square_mem_halfProductSource_iff {num den N r : ℕ} {T : ℝ}
    (hr : Nat.Prime r) :
    r * r ∈ halfProductSource num den N T ↔
      r * r ≤ N ∧ T ≤ (r * r : ℕ) ∧ r ^ num < r ^ den := by
  constructor
  · intro hm
    obtain ⟨hN, hcut, s, t, hs, ht, hmul, hst, hpow⟩ :=
      mem_halfProductSource_iff_ordered_factors.mp hm
    obtain ⟨hsr, htr⟩ :=
      ordered_prime_factors_unique hs ht hr hr hst (le_refl r) hmul.symm
    exact ⟨hN, hcut, by simpa only [hsr, htr] using hpow⟩
  · rintro ⟨hN, hcut, hpow⟩
    exact mem_halfProductSource_iff_ordered_factors.mpr
      ⟨hN, hcut, r, r, hr, hr, rfl, le_refl r, hpow⟩

/-- The actual retained bad count is an ordered-pair prime-partner count,
with neither multiplicity loss nor any omitted square correction. -/
theorem retainedBadReceiversReal_card_eq_halfProductPairs_filter_card
    (num den N : ℕ) (T : ℝ) :
    (retainedBadReceiversReal num den N T).card =
      ((halfProductPairs num den N T).filter
        (fun a => a.1 * a.2 < N ∧ Nat.Prime (N - a.1 * a.2))).card := by
  classical
  rw [retainedBadReceiversReal_eq_halfProductSource_filter]
  exact (halfProductPairs_filter_card_eq num den N T
    (fun m => m < N ∧ Nat.Prime (N - m))).symm

/-- The original bad count is the sieved half-product count plus the exact
small-receiver contribution. This identifies the finite source for a future
sieve theorem; it is not itself a sieve estimate. -/
theorem B_eq_halfProductSource_filter_card_add_small
    (num den N : ℕ) (T : ℝ) :
    B num den N =
      ((halfProductSource num den N T).filter
        (fun m => m < N ∧ Nat.Prime (N - m))).card +
      (smallBadReceiversReal num den N T).card := by
  rw [← retainedBadReceiversReal_eq_halfProductSource_filter]
  exact B_eq_retainedBadReceiversReal_card_add_smallBadReceiversReal_card num den N T

/-- Finite localization expressed directly with the manuscript's sieve source. -/
theorem B_cast_le_halfProductSource_filter_card_add_cutoff
    (num den N : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    (B num den N : ℝ) ≤
      ((halfProductSource num den N T).filter
        (fun m => m < N ∧ Nat.Prime (N - m))).card + (T + 1) := by
  classical
  rw [← retainedBadReceiversReal_eq_halfProductSource_filter]
  exact B_cast_le_retainedBadReceiversReal_card_add_cutoff num den N hT

/-- Every member of the actual half-product source has the strictly rough
ordered factors supplied by the elementary geometry. -/
theorem halfProductSource_exists_rough_factors {num den N m : ℕ} {T : ℝ}
    (hnum : 0 < num) (hden : 0 < den) (hT : 0 < T)
    (hm : m ∈ halfProductSource num den N T) :
    m ≤ N ∧ T ≤ (m : ℝ) ∧
      ∃ r q : ℕ, Nat.Prime r ∧ Nat.Prime q ∧ m = r * q ∧ r ≤ q ∧
        (q : ℝ) ^ ((num : ℝ) / (den : ℝ)) < (r : ℝ) ∧
        T ^ (((num : ℝ) / (den : ℝ)) /
          (1 + (num : ℝ) / (den : ℝ))) < (r : ℝ) ∧
        T ^ (((num : ℝ) / (den : ℝ)) /
          (1 + (num : ℝ) / (den : ℝ))) < (q : ℝ) := by
  rcases mem_halfProductSource.mp hm with ⟨hN, hcut, hbad⟩
  exact ⟨hN, hcut, badReceiver_exists_rough_factors hnum hden hT
    (badReceiver_iff_orderedBadReceiver.mpr hbad) hcut⟩

end

end ImbalancedChen
