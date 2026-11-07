import ImbalancedChen.CurrentMainTheorem
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Finset.Prod
import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega

/-!
# Arbitrary-real half-product source

This file connects the arbitrary real exponent in the current statement of
Theorem 1.1 to the finite ordered half-product source used by the sieve.  The
complement map `p ↦ N - p` is an exact bijection from bad additive primes to
bad receivers.  A real cutoff partitions this receiver set exactly, and the
retained set is precisely the half-product source filtered by the original
additive-prime condition.

Multiplication is a bijection from ordered prime-factor pairs to source
integers, including prime squares.  Hence none of these changes of index
introduces a factor of two or factor-witness multiplicity.  All results here
are finite identities; no prime-distribution or sieve estimate is assumed.
-/

namespace ImbalancedChen

noncomputable section

/-- The current ordered bad set indexed by its receiver rather than by the
additive prime.  The strict upper endpoint records the original `p < N`. -/
def realBadReceivers (b : ℝ) (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range N).filter fun m =>
    0 < m ∧ Nat.Prime (N - m) ∧ RealOrderedBadReceiver b m

@[simp] theorem mem_realBadReceivers {b : ℝ} {N m : ℕ} :
    m ∈ realBadReceivers b N ↔
      m < N ∧ 0 < m ∧ Nat.Prime (N - m) ∧ RealOrderedBadReceiver b m := by
  classical
  simp only [realBadReceivers, Finset.mem_filter, Finset.mem_range]

theorem sub_mem_realBadReceivers_of_mem_realOrderedBadPrimes
    {b : ℝ} {N p : ℕ} (hp : p ∈ realOrderedBadPrimes b N) :
    N - p ∈ realBadReceivers b N := by
  rcases mem_realOrderedBadPrimes.mp hp with ⟨hpN, hpprime, hbad⟩
  have hp0 : 0 < p := hpprime.pos
  have hinv : N - (N - p) = p := by omega
  exact mem_realBadReceivers.mpr
    ⟨by omega, by omega, by simpa only [hinv] using hpprime, hbad⟩

theorem sub_mem_realOrderedBadPrimes_of_mem_realBadReceivers
    {b : ℝ} {N m : ℕ} (hm : m ∈ realBadReceivers b N) :
    N - m ∈ realOrderedBadPrimes b N := by
  rcases mem_realBadReceivers.mp hm with ⟨hmN, hm0, hpprime, hbad⟩
  have hinv : N - (N - m) = m := by omega
  exact mem_realOrderedBadPrimes.mpr
    ⟨by omega, hpprime, by simpa only [hinv] using hbad⟩

/-- Exact reindexing of the current bad count. -/
theorem RealB_eq_realBadReceivers_card {b : ℝ} (hb : b < 1) (N : ℕ) :
    RealB b N = (realBadReceivers b N).card := by
  rw [RealB_eq_realOrderedBadPrimes_card hb]
  refine Finset.card_bij' (fun p _ => N - p) (fun m _ => N - m)
    (fun _ hp => sub_mem_realBadReceivers_of_mem_realOrderedBadPrimes hp)
    (fun _ hm => sub_mem_realOrderedBadPrimes_of_mem_realBadReceivers hm) ?_ ?_
  · intro p hp
    have hpN := (mem_realOrderedBadPrimes.mp hp).1
    omega
  · intro m hm
    have hmN := (mem_realBadReceivers.mp hm).1
    omega

/-- The retained receiver source at the literal real cutoff `T`. -/
def retainedRealBadReceivers (b : ℝ) (N : ℕ) (T : ℝ) : Finset ℕ := by
  classical
  exact (realBadReceivers b N).filter fun m => T ≤ (m : ℝ)

/-- The complementary small-receiver contribution. -/
def smallRealBadReceivers (b : ℝ) (N : ℕ) (T : ℝ) : Finset ℕ := by
  classical
  exact (realBadReceivers b N).filter fun m => (m : ℝ) < T

@[simp] theorem mem_retainedRealBadReceivers {b T : ℝ} {N m : ℕ} :
    m ∈ retainedRealBadReceivers b N T ↔
      m ∈ realBadReceivers b N ∧ T ≤ (m : ℝ) := by
  classical
  simp only [retainedRealBadReceivers, Finset.mem_filter]

@[simp] theorem mem_smallRealBadReceivers {b T : ℝ} {N m : ℕ} :
    m ∈ smallRealBadReceivers b N T ↔
      m ∈ realBadReceivers b N ∧ (m : ℝ) < T := by
  classical
  simp only [smallRealBadReceivers, Finset.mem_filter]

/-- Exact finite cutoff partition of the current bad count. -/
theorem RealB_eq_retainedRealBadReceivers_card_add_smallRealBadReceivers_card
    {b : ℝ} (hb : b < 1) (N : ℕ) (T : ℝ) :
    RealB b N = (retainedRealBadReceivers b N T).card +
      (smallRealBadReceivers b N T).card := by
  classical
  rw [RealB_eq_realBadReceivers_card hb]
  have h := Finset.card_filter_add_card_filter_not
    (s := realBadReceivers b N) (fun m : ℕ => T ≤ (m : ℝ))
  simpa only [retainedRealBadReceivers, smallRealBadReceivers, not_le] using h.symm

/-- Small receivers inject into `[0, ceil T)`. -/
theorem smallRealBadReceivers_subset_range (b : ℝ) (N : ℕ) (T : ℝ) :
    smallRealBadReceivers b N T ⊆ Finset.range (Nat.ceil T) := by
  intro m hm
  exact Finset.mem_range.mpr (Nat.lt_ceil.mpr (mem_smallRealBadReceivers.mp hm).2)

theorem smallRealBadReceivers_card_le_ceil (b : ℝ) (N : ℕ) (T : ℝ) :
    (smallRealBadReceivers b N T).card ≤ Nat.ceil T := by
  calc
    (smallRealBadReceivers b N T).card ≤ (Finset.range (Nat.ceil T)).card :=
      Finset.card_le_card (smallRealBadReceivers_subset_range b N T)
    _ = Nat.ceil T := Finset.card_range _

theorem smallRealBadReceivers_cast_card_lt {b T : ℝ} {N : ℕ} (hT : 0 ≤ T) :
    ((smallRealBadReceivers b N T).card : ℝ) < T + 1 := by
  have hcard : ((smallRealBadReceivers b N T).card : ℝ) ≤ (Nat.ceil T : ℝ) :=
    Nat.cast_le.mpr (smallRealBadReceivers_card_le_ceil b N T)
  exact hcard.trans_lt (Nat.ceil_lt_add_one hT)

/-- The arbitrary-real ordered half-product source, with inclusive product
upper endpoint and literal strict power boundary. -/
def realHalfProductSource (b : ℝ) (N : ℕ) (T : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range (N + 1)).filter fun m =>
    T ≤ (m : ℝ) ∧ RealOrderedBadReceiver b m

@[simp] theorem mem_realHalfProductSource {b T : ℝ} {N m : ℕ} :
    m ∈ realHalfProductSource b N T ↔
      m ≤ N ∧ T ≤ (m : ℝ) ∧ RealOrderedBadReceiver b m := by
  classical
  simp only [realHalfProductSource, Finset.mem_filter, Finset.mem_range,
    Nat.lt_succ_iff]

theorem realHalfProductSource_pos {b T : ℝ} {N m : ℕ}
    (hm : m ∈ realHalfProductSource b N T) : 0 < m := by
  obtain ⟨_, _, r, q, hr, hq, hmul, _, _⟩ := mem_realHalfProductSource.mp hm
  rw [hmul]
  exact Nat.mul_pos hr.pos hq.pos

/-- The retained actual receiver set is exactly the source filtered by the
original additive-prime condition. -/
theorem retainedRealBadReceivers_eq_realHalfProductSource_filter
    (b : ℝ) (N : ℕ) (T : ℝ) :
    retainedRealBadReceivers b N T =
      (realHalfProductSource b N T).filter
        (fun m => m < N ∧ Nat.Prime (N - m)) := by
  classical
  ext m
  rw [mem_retainedRealBadReceivers, Finset.mem_filter]
  constructor
  · rintro ⟨hmem, hcut⟩
    rcases mem_realBadReceivers.mp hmem with ⟨hmN, _, hp, hbad⟩
    exact ⟨mem_realHalfProductSource.mpr ⟨hmN.le, hcut, hbad⟩, hmN, hp⟩
  · rintro ⟨hmem, hmN, hp⟩
    rcases mem_realHalfProductSource.mp hmem with ⟨_, hcut, hbad⟩
    exact ⟨mem_realBadReceivers.mpr
      ⟨hmN, realHalfProductSource_pos hmem, hp, hbad⟩, hcut⟩

/-- Ordered pairs whose products form the arbitrary-real source. -/
def realHalfProductPairs (b : ℝ) (N : ℕ) (T : ℝ) : Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.range (N + 1)).product (Finset.range (N + 1))).filter fun a =>
    Nat.Prime a.1 ∧ Nat.Prime a.2 ∧ a.1 ≤ a.2 ∧
      (a.2 : ℝ) ^ b < (a.1 : ℝ) ∧
      T ≤ (a.1 * a.2 : ℕ) ∧ a.1 * a.2 ≤ N

@[simp] theorem mem_realHalfProductPairs {b T : ℝ} {N r q : ℕ} :
    (r, q) ∈ realHalfProductPairs b N T ↔
      Nat.Prime r ∧ Nat.Prime q ∧ r ≤ q ∧
        (q : ℝ) ^ b < (r : ℝ) ∧ T ≤ (r * q : ℕ) ∧ r * q ≤ N := by
  classical
  unfold realHalfProductPairs
  rw [Finset.mem_filter]
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
    exact ⟨Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hrN),
        Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hqN)⟩, h⟩

theorem mul_mem_realHalfProductSource {b T : ℝ} {N : ℕ} {a : ℕ × ℕ}
    (ha : a ∈ realHalfProductPairs b N T) :
    a.1 * a.2 ∈ realHalfProductSource b N T := by
  rcases a with ⟨r, q⟩
  rcases mem_realHalfProductPairs.mp ha with ⟨hr, hq, hrq, hpow, hcut, hN⟩
  exact mem_realHalfProductSource.mpr
    ⟨hN, hcut, r, q, hr, hq, rfl, hrq, hpow⟩

theorem realHalfProductPairs_mul_injective {b T : ℝ} {N : ℕ}
    {a c : ℕ × ℕ} (ha : a ∈ realHalfProductPairs b N T)
    (hc : c ∈ realHalfProductPairs b N T) (hmul : a.1 * a.2 = c.1 * c.2) :
    a = c := by
  rcases a with ⟨r, q⟩
  rcases c with ⟨s, t⟩
  rcases mem_realHalfProductPairs.mp ha with ⟨hr, hq, hrq, _, _, _⟩
  rcases mem_realHalfProductPairs.mp hc with ⟨hs, ht, hst, _, _, _⟩
  obtain ⟨hrs, hqt⟩ := ordered_prime_factors_unique hr hq hs ht hrq hst hmul
  exact Prod.ext hrs hqt

theorem realHalfProductSource_existsUnique_pair {b T : ℝ} {N m : ℕ}
    (hm : m ∈ realHalfProductSource b N T) :
    ∃! a : ℕ × ℕ,
      a ∈ realHalfProductPairs b N T ∧ a.1 * a.2 = m := by
  obtain ⟨hN, hcut, r, q, hr, hq, hmul, hrq, hpow⟩ :=
    mem_realHalfProductSource.mp hm
  have hp : (r, q) ∈ realHalfProductPairs b N T :=
    mem_realHalfProductPairs.mpr
      ⟨hr, hq, hrq, hpow, hmul ▸ hcut, hmul ▸ hN⟩
  refine ⟨(r, q), ⟨hp, hmul.symm⟩, ?_⟩
  intro a ha
  exact realHalfProductPairs_mul_injective ha.1 hp (ha.2.trans hmul)

theorem realHalfProductPairs_card_eq (b : ℝ) (N : ℕ) (T : ℝ) :
    (realHalfProductPairs b N T).card = (realHalfProductSource b N T).card := by
  classical
  refine Finset.card_bij (fun a _ => a.1 * a.2) ?_ ?_ ?_
  · intro a ha
    exact mul_mem_realHalfProductSource ha
  · intro a ha c hc hmul
    exact realHalfProductPairs_mul_injective ha hc hmul
  · intro m hm
    obtain ⟨a, ha, _⟩ := realHalfProductSource_existsUnique_pair hm
    exact ⟨a, ha.1, ha.2⟩

/-- Final exact finite bridge: the current bad count is a sieved
arbitrary-real half-product count plus only the proved small range. -/
theorem RealB_eq_realHalfProductSource_filter_card_add_small
    {b : ℝ} (hb : b < 1) (N : ℕ) (T : ℝ) :
    RealB b N =
      ((realHalfProductSource b N T).filter
        (fun m => m < N ∧ Nat.Prime (N - m))).card +
      (smallRealBadReceivers b N T).card := by
  rw [← retainedRealBadReceivers_eq_realHalfProductSource_filter]
  exact RealB_eq_retainedRealBadReceivers_card_add_smallRealBadReceivers_card
    hb N T

end

end ImbalancedChen
