import ImbalancedChen.HalfProductGeometry
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Finset.Card
import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega

/-!
# Finite localization of the actual bad source

The manuscript's bad count `B` is indexed by additive primes `p < N`.
The complement map `p ↦ N - p` is a bijection from that finite set to the
bad receivers `0 < m < N` for which the additive partner `N - m` is prime.
Thus changing the index to the receiver introduces neither a counting loss
nor a new source set. In particular, the additive-prime condition is kept.

For a natural-number cutoff `T`, we partition this receiver set into the
retained receivers `T ≤ m` and the discarded receivers `m < T`. Inclusion
of the discarded set into `Finset.range T` gives its cardinality bound.
The retained set also satisfies the ordered bad-factor and strict roughness
conditions proved in `HalfProductGeometry`.

Real cutoffs use `Nat.ceil T`, which gives exactly the condition `T ≤ m`
on natural receivers. For nonnegative real `T`, the discarded contribution
is at most `T + 1`; the retained source is not weakened by rounding down.

All counts are of receivers, never of choices of prime-factor witnesses.
Prime squares are therefore counted once. These are exact finite statements;
no sieve bound, prime-counting asymptotic, or analytic estimate is assumed.
-/

namespace ImbalancedChen

noncomputable section

/-- The actual bad source, now indexed by the receiver. The strict upper
bound and the positive receiver encode the original strict condition `p < N`,
while `Nat.Prime (N - m)` retains the additive-prime restriction. -/
def badReceivers (num den N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range N).filter fun m =>
    0 < m ∧ Nat.Prime (N - m) ∧ BadReceiver num den m

@[simp] theorem mem_badReceivers {num den N m : ℕ} :
    m ∈ badReceivers num den N ↔
      m < N ∧ 0 < m ∧ Nat.Prime (N - m) ∧ BadReceiver num den m := by
  classical
  simp only [badReceivers, Finset.mem_filter, Finset.mem_range]

/-- The complement of an actual bad additive prime is an actual bad receiver. -/
theorem sub_mem_badReceivers_of_mem_badPrimes {num den N p : ℕ}
    (hp : p ∈ badPrimes num den N) :
    N - p ∈ badReceivers num den N := by
  classical
  have hp' : p < N ∧ Nat.Prime p ∧ BadReceiver num den (N - p) := by
    simpa only [badPrimes, Finset.mem_filter, Finset.mem_range] using hp
  rcases hp' with ⟨hpN, hpprime, hbad⟩
  have hp0 : 0 < p := hpprime.pos
  have hinv : N - (N - p) = p := by omega
  exact mem_badReceivers.mpr
    ⟨by omega, by omega, by simpa only [hinv] using hpprime, hbad⟩

/-- Taking the complement back preserves the original prime-indexed source. -/
theorem sub_mem_badPrimes_of_mem_badReceivers {num den N m : ℕ}
    (hm : m ∈ badReceivers num den N) :
    N - m ∈ badPrimes num den N := by
  classical
  rcases mem_badReceivers.mp hm with ⟨hmN, hm0, hpprime, hbad⟩
  have hinv : N - (N - m) = m := by omega
  have h : N - m < N ∧ Nat.Prime (N - m) ∧
      BadReceiver num den (N - (N - m)) :=
    ⟨by omega, hpprime, by simpa only [hinv] using hbad⟩
  simpa only [badPrimes, Finset.mem_filter, Finset.mem_range] using h

/-- Exact reindexing of `B` by receivers. Both directions use the same
complement involution, so distinct representations cannot be merged. -/
theorem B_eq_badReceivers_card (num den N : ℕ) :
    B num den N = (badReceivers num den N).card := by
  unfold B
  refine Finset.card_bij' (fun p _ => N - p) (fun m _ => N - m)
    (fun _ hp => sub_mem_badReceivers_of_mem_badPrimes hp)
    (fun _ hm => sub_mem_badPrimes_of_mem_badReceivers hm) ?_ ?_
  · intro p hp
    have hpN := (mem_badPrimes.mp hp).1
    omega
  · intro m hm
    have hmN := (mem_badReceivers.mp hm).1
    omega

/-- Receiver membership is exactly the ordered bad-factor region together
with its original additive-prime restriction. -/
theorem mem_badReceivers_iff_ordered_factors {num den N m : ℕ} :
    m ∈ badReceivers num den N ↔
      m < N ∧ 0 < m ∧ Nat.Prime (N - m) ∧
        ∃ r q : ℕ, Nat.Prime r ∧ Nat.Prime q ∧ m = r * q ∧
          r ≤ q ∧ q ^ num < r ^ den := by
  rw [mem_badReceivers, badReceiver_iff_ordered_factors]

/-- Actual bad receivers above the lower cutoff, still with prime partners. -/
def retainedBadReceivers (num den N T : ℕ) : Finset ℕ := by
  classical
  exact (badReceivers num den N).filter fun m => T ≤ m

/-- The complementary small-receiver contribution to the actual count. -/
def smallBadReceivers (num den N T : ℕ) : Finset ℕ := by
  classical
  exact (badReceivers num den N).filter fun m => m < T

@[simp] theorem mem_retainedBadReceivers {num den N T m : ℕ} :
    m ∈ retainedBadReceivers num den N T ↔
      m ∈ badReceivers num den N ∧ T ≤ m := by
  classical
  simp only [retainedBadReceivers, Finset.mem_filter]

@[simp] theorem mem_smallBadReceivers {num den N T m : ℕ} :
    m ∈ smallBadReceivers num den N T ↔
      m ∈ badReceivers num den N ∧ m < T := by
  classical
  simp only [smallBadReceivers, Finset.mem_filter]

/-- A direct ordered-factor characterization of the retained source. -/
theorem mem_retainedBadReceivers_iff_ordered_factors {num den N T m : ℕ} :
    m ∈ retainedBadReceivers num den N T ↔
      m < N ∧ 0 < m ∧ T ≤ m ∧ Nat.Prime (N - m) ∧
        ∃ r q : ℕ, Nat.Prime r ∧ Nat.Prime q ∧ m = r * q ∧
          r ≤ q ∧ q ^ num < r ^ den := by
  rw [mem_retainedBadReceivers, mem_badReceivers_iff_ordered_factors]
  constructor
  · rintro ⟨⟨hmN, hm0, hpprime, hfactors⟩, hcut⟩
    exact ⟨hmN, hm0, hcut, hpprime, hfactors⟩
  · rintro ⟨hmN, hm0, hcut, hpprime, hfactors⟩
    exact ⟨⟨hmN, hm0, hpprime, hfactors⟩, hcut⟩

/-- Exact finite cutoff partition of the manuscript's original bad count. -/
theorem B_eq_retainedBadReceivers_card_add_smallBadReceivers_card
    (num den N T : ℕ) :
    B num den N = (retainedBadReceivers num den N T).card +
      (smallBadReceivers num den N T).card := by
  classical
  rw [B_eq_badReceivers_card]
  have h := Finset.card_filter_add_card_filter_not
    (s := badReceivers num den N) (fun m => T ≤ m)
  simpa only [retainedBadReceivers, smallBadReceivers, not_le] using h.symm

/-- Inclusion into the finite interval `[0,T)` is the small-range injection.
It is valid also for `T = 0` and for cutoffs above `N`. -/
theorem smallBadReceivers_subset_range (num den N T : ℕ) :
    smallBadReceivers num den N T ⊆ Finset.range T := by
  intro m hm
  exact Finset.mem_range.mpr (mem_smallBadReceivers.mp hm).2

/-- The discarded contribution has at most `T` distinct receivers. -/
theorem smallBadReceivers_card_le (num den N T : ℕ) :
    (smallBadReceivers num den N T).card ≤ T := by
  calc
    (smallBadReceivers num den N T).card ≤ (Finset.range T).card :=
      Finset.card_le_card (smallBadReceivers_subset_range num den N T)
    _ = T := Finset.card_range T

/-- Finite localization of the actual source: the only loss is a proved
small-range cardinality bound, with no analytic premise. -/
theorem B_le_retainedBadReceivers_card_add_cutoff (num den N T : ℕ) :
    B num den N ≤ (retainedBadReceivers num den N T).card + T := by
  rw [B_eq_retainedBadReceivers_card_add_smallBadReceivers_card num den N T]
  exact Nat.add_le_add_left (smallBadReceivers_card_le num den N T) _

/-- Real-valued version for subsequent normalization estimates. -/
theorem B_cast_le_retainedBadReceivers_card_add_cutoff (num den N T : ℕ) :
    (B num den N : ℝ) ≤ (retainedBadReceivers num den N T).card + (T : ℝ) := by
  exact_mod_cast B_le_retainedBadReceivers_card_add_cutoff num den N T

/-- Every retained receiver belongs to the actual prime-partner source and
has the ordered rough factors needed by the half-product geometry. -/
theorem retainedBadReceivers_exists_rough_factors {num den N T m : ℕ}
    (hnum : 0 < num) (hden : 0 < den) (hT : 0 < T)
    (hm : m ∈ retainedBadReceivers num den N T) :
    0 < m ∧ m < N ∧ T ≤ m ∧ Nat.Prime (N - m) ∧
      ∃ r q : ℕ, Nat.Prime r ∧ Nat.Prime q ∧ m = r * q ∧ r ≤ q ∧
        (q : ℝ) ^ ((num : ℝ) / (den : ℝ)) < (r : ℝ) ∧
        (T : ℝ) ^ (((num : ℝ) / (den : ℝ)) /
          (1 + (num : ℝ) / (den : ℝ))) < (r : ℝ) ∧
        (T : ℝ) ^ (((num : ℝ) / (den : ℝ)) /
          (1 + (num : ℝ) / (den : ℝ))) < (q : ℝ) := by
  rcases mem_retainedBadReceivers.mp hm with ⟨hmem, hcut⟩
  rcases mem_badReceivers.mp hmem with ⟨hmN, hm0, hpprime, hbad⟩
  exact ⟨hm0, hmN, hcut, hpprime,
    badReceiver_exists_rough_factors hnum hden (Nat.cast_pos.mpr hT) hbad
      (Nat.cast_le.mpr hcut)⟩

/-- A real lower cutoff, implemented by the exact ceiling on natural receivers. -/
def retainedBadReceiversReal (num den N : ℕ) (T : ℝ) : Finset ℕ :=
  retainedBadReceivers num den N (Nat.ceil T)

/-- The small contribution complementary to a real lower cutoff. -/
def smallBadReceiversReal (num den N : ℕ) (T : ℝ) : Finset ℕ :=
  smallBadReceivers num den N (Nat.ceil T)

/-- Ceiling implements the literal real inequality without any change of
source. No sign assumption on `T` is required for this equivalence. -/
@[simp] theorem mem_retainedBadReceiversReal {num den N m : ℕ} {T : ℝ} :
    m ∈ retainedBadReceiversReal num den N T ↔
      m ∈ badReceivers num den N ∧ T ≤ (m : ℝ) := by
  rw [retainedBadReceiversReal, mem_retainedBadReceivers, Nat.ceil_le]

@[simp] theorem mem_smallBadReceiversReal {num den N m : ℕ} {T : ℝ} :
    m ∈ smallBadReceiversReal num den N T ↔
      m ∈ badReceivers num den N ∧ (m : ℝ) < T := by
  rw [smallBadReceiversReal, mem_smallBadReceivers, Nat.lt_ceil]

/-- The ceiling-defined source is exactly the finite source filtered by
the manuscript's real cutoff inequality. -/
theorem retainedBadReceiversReal_eq_filter (num den N : ℕ) (T : ℝ) :
    retainedBadReceiversReal num den N T =
      (badReceivers num den N).filter (fun m : ℕ => T ≤ (m : ℝ)) := by
  classical
  ext m
  simp only [mem_retainedBadReceiversReal, Finset.mem_filter]

/-- The real cutoff also gives an exact partition, before estimating the loss. -/
theorem B_eq_retainedBadReceiversReal_card_add_smallBadReceiversReal_card
    (num den N : ℕ) (T : ℝ) :
    B num den N = (retainedBadReceiversReal num den N T).card +
      (smallBadReceiversReal num den N T).card :=
  B_eq_retainedBadReceivers_card_add_smallBadReceivers_card num den N (Nat.ceil T)

/-- A real cutoff loses fewer than `T + 1` receivers, using the finite
injection already proved at the natural cutoff `Nat.ceil T`. -/
theorem smallBadReceiversReal_card_lt (num den N : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    ((smallBadReceiversReal num den N T).card : ℝ) < T + 1 := by
  have hcard : ((smallBadReceiversReal num den N T).card : ℝ) ≤
      (Nat.ceil T : ℝ) :=
    Nat.cast_le.mpr (smallBadReceivers_card_le num den N (Nat.ceil T))
  exact lt_of_le_of_lt hcard (Nat.ceil_lt_add_one hT)

/-- Finite localization for a nonnegative real cutoff, with the exact
retained source and an explicit rounding loss of at most one. -/
theorem B_cast_le_retainedBadReceiversReal_card_add_cutoff
    (num den N : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    (B num den N : ℝ) ≤ (retainedBadReceiversReal num den N T).card + (T + 1) := by
  calc
    (B num den N : ℝ) ≤ (retainedBadReceiversReal num den N T).card +
        (Nat.ceil T : ℝ) :=
      B_cast_le_retainedBadReceivers_card_add_cutoff num den N (Nat.ceil T)
    _ ≤ (retainedBadReceiversReal num den N T).card + (T + 1) :=
      add_le_add le_rfl (Nat.ceil_lt_add_one hT).le

/-- Real-cutoff roughness is stated at the original real `T`, while preserving
the prime partner and the exact finite retained source. -/
theorem retainedBadReceiversReal_exists_rough_factors {num den N m : ℕ} {T : ℝ}
    (hnum : 0 < num) (hden : 0 < den) (hT : 0 < T)
    (hm : m ∈ retainedBadReceiversReal num den N T) :
    0 < m ∧ m < N ∧ T ≤ (m : ℝ) ∧ Nat.Prime (N - m) ∧
      ∃ r q : ℕ, Nat.Prime r ∧ Nat.Prime q ∧ m = r * q ∧ r ≤ q ∧
        (q : ℝ) ^ ((num : ℝ) / (den : ℝ)) < (r : ℝ) ∧
        T ^ (((num : ℝ) / (den : ℝ)) /
          (1 + (num : ℝ) / (den : ℝ))) < (r : ℝ) ∧
        T ^ (((num : ℝ) / (den : ℝ)) /
          (1 + (num : ℝ) / (den : ℝ))) < (q : ℝ) := by
  rcases mem_retainedBadReceiversReal.mp hm with ⟨hmem, hcut⟩
  rcases mem_badReceivers.mp hmem with ⟨hmN, hm0, hpprime, hbad⟩
  exact ⟨hm0, hmN, hcut, hpprime,
    badReceiver_exists_rough_factors hnum hden hT hbad hcut⟩

end

end ImbalancedChen
