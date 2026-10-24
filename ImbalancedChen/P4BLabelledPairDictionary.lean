import ImbalancedChen.RealHalfProductSource
import ImbalancedChen.Part3DistributionTargets
import ImbalancedChen.RealPhysicalUpperWeightBridge
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Genuine rank-two labelled dictionary for the actual ordered source

YELLOW / SOURCE-ONLY / UNCOMPILED DRAFT.

The weight below is the literal indicator of the ordered curved region,
independent of the modulus. The prime condition is supplied by the existing
labelled prime carrier. The product reindexing uses the proved uniqueness
of ordered prime factors, including repeated primes. The final equality
identifies the actual signed errors; it assumes neither that equality nor
any Part 3 distribution estimate or geometric licence.
-/

namespace ImbalancedChen.P4BLabelledPairDictionary

noncomputable section

open scoped BigOperators
open ImbalancedChen.Part3

/-- Read the two labelled coordinates as an ordered natural pair. -/
def tuplePair {N : ℕ} (t : Fin 2 → Fin (N + 1)) : ℕ × ℕ :=
  ((t 0).val, (t 1).val)

/-- Embed a bounded actual pair in the genuine rank-two labelled carrier. -/
def pairTuple (N : ℕ) (a : ℕ × ℕ) (hr : a.1 ≤ N) (hq : a.2 ≤ N) :
    Fin 2 → Fin (N + 1) :=
  ![⟨a.1, Nat.lt_succ_iff.mpr hr⟩, ⟨a.2, Nat.lt_succ_iff.mpr hq⟩]

@[simp] theorem tuplePair_pairTuple (N : ℕ) (a : ℕ × ℕ)
    (hr : a.1 ≤ N) (hq : a.2 ≤ N) :
    tuplePair (pairTuple N a hr hq) = a := by
  rcases a with ⟨r, q⟩
  simp [tuplePair, pairTuple]

theorem tuplePair_injective (N : ℕ) :
    Function.Injective (@tuplePair N) := by
  intro t u h
  funext i
  fin_cases i
  · apply Fin.ext
    simpa only [tuplePair] using congrArg Prod.fst h
  · apply Fin.ext
    simpa only [tuplePair] using congrArg Prod.snd h

@[simp] theorem labelledProduct_eq_pairProduct {N : ℕ}
    (t : Fin 2 → Fin (N + 1)) :
    labelledProduct t = (tuplePair t).1 * (tuplePair t).2 := by
  simp only [labelledProduct, Fin.prod_univ_two, tuplePair]

@[simp] theorem labelledProduct_pairTuple (N : ℕ) (a : ℕ × ℕ)
    (hr : a.1 ≤ N) (hq : a.2 ≤ N) :
    labelledProduct (pairTuple N a hr hq) = a.1 * a.2 := by
  rw [labelledProduct_eq_pairProduct, tuplePair_pairTuple]

/-- Inclusive upper product endpoint and literal strict real-power wall. -/
def geometry (b : ℝ) (N : ℕ) (T : ℝ)
    (t : Fin 2 → Fin (N + 1)) : Prop :=
  (tuplePair t).1 ≤ (tuplePair t).2 ∧
    ((tuplePair t).2 : ℝ) ^ b < ((tuplePair t).1 : ℝ) ∧
    T ≤ ((tuplePair t).1 * (tuplePair t).2 : ℕ) ∧
    (tuplePair t).1 * (tuplePair t).2 ≤ N

/-- The genuine fixed-source geometric indicator; there is no modulus
argument, chosen error value, analytic estimate, or artificial rescaling. -/
def W (b : ℝ) (N : ℕ) (T : ℝ)
    (t : Fin 2 → Fin (N + 1)) : ℝ := by
  classical
  exact if geometry b N T t then 1 else 0

/-- Exactly the labelled prime tuples on which the geometric weight is one. -/
def activeCarrier (b : ℝ) (N : ℕ) (T : ℝ) :
    Finset (Fin 2 → Fin (N + 1)) := by
  classical
  exact (labelledPrimeTuples 2 N).filter (geometry b N T)

theorem W_nonneg (b : ℝ) (N : ℕ) (T : ℝ)
    (t : Fin 2 → Fin (N + 1)) : 0 ≤ W b N T t := by
  classical
  unfold W
  split_ifs <;> norm_num

theorem W_le_one (b : ℝ) (N : ℕ) (T : ℝ)
    (t : Fin 2 → Fin (N + 1)) : W b N T t ≤ 1 := by
  classical
  unfold W
  split_ifs <;> norm_num

/-- The literal carrier dictionary, in both directions. -/
theorem mem_activeCarrier_iff {b T : ℝ} {N : ℕ}
    (t : Fin 2 → Fin (N + 1)) :
    t ∈ activeCarrier b N T ↔ tuplePair t ∈ realHalfProductPairs b N T := by
  classical
  rw [activeCarrier, Finset.mem_filter]
  constructor
  · rintro ⟨ht, hgeometry⟩
    have hp : ∀ i : Fin 2, Nat.Prime (t i).val :=
      (Finset.mem_filter.mp ht).2
    exact mem_realHalfProductPairs.mpr
      ⟨hp 0, hp 1, hgeometry.1, hgeometry.2.1,
        hgeometry.2.2.1, hgeometry.2.2.2⟩
  · intro ht
    rcases mem_realHalfProductPairs.mp ht with
      ⟨hr, hq, horder, hpower, hcutoff, hproduct⟩
    refine ⟨?_, ⟨horder, hpower, hcutoff, hproduct⟩⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro i
    fin_cases i
    · exact hr
    · exact hq

/-- Actual pair coordinates fit the same finite cap N, without enlarging
the source or requiring distinct primes. -/
theorem pair_coordinates_le {b T : ℝ} {N : ℕ} {a : ℕ × ℕ}
    (ha : a ∈ realHalfProductPairs b N T) : a.1 ≤ N ∧ a.2 ≤ N := by
  rcases a with ⟨r, q⟩
  rcases mem_realHalfProductPairs.mp ha with ⟨hr, hq, _, _, _, hproduct⟩
  constructor
  · calc
      r = r * 1 := (Nat.mul_one r).symm
      _ ≤ r * q := Nat.mul_le_mul_left r hq.one_le
      _ ≤ N := hproduct
  · calc
      q = 1 * q := (Nat.one_mul q).symm
      _ ≤ r * q := Nat.mul_le_mul_right q hr.one_le
      _ ≤ N := hproduct

/-- Every actual ordered prime pair has a concrete active labelled image. -/
theorem pairTuple_mem_activeCarrier {b T : ℝ} {N : ℕ} {a : ℕ × ℕ}
    (ha : a ∈ realHalfProductPairs b N T) :
    pairTuple N a (pair_coordinates_le ha).1 (pair_coordinates_le ha).2 ∈
      activeCarrier b N T := by
  rw [mem_activeCarrier_iff, tuplePair_pairTuple]
  exact ha

/-- First exact sum bijection: active labelled tuples and actual ordered
pairs, with the labelled product preserved literally. -/
theorem sum_activeCarrier_eq_pairs (b : ℝ) (N : ℕ) (T : ℝ) (F : ℕ → ℝ) :
    (∑ t ∈ activeCarrier b N T, F (labelledProduct t)) =
      ∑ a ∈ realHalfProductPairs b N T, F (a.1 * a.2) := by
  classical
  refine Finset.sum_bij (fun t _ => tuplePair t) ?_ ?_ ?_ ?_
  · intro t ht
    exact (mem_activeCarrier_iff t).mp ht
  · intro t ht u hu htu
    exact tuplePair_injective N htu
  · intro a ha
    refine ⟨pairTuple N a (pair_coordinates_le ha).1 (pair_coordinates_le ha).2,
      pairTuple_mem_activeCarrier ha, ?_⟩
    exact tuplePair_pairTuple _ _ _ _
  · intro t ht
    rw [labelledProduct_eq_pairProduct]

/-- Second exact sum bijection: multiply actual ordered pairs. Existing
ordered-prime-factor uniqueness prevents any multiplicity or factor two. -/
theorem sum_pairs_eq_source (b : ℝ) (N : ℕ) (T : ℝ) (F : ℕ → ℝ) :
    (∑ a ∈ realHalfProductPairs b N T, F (a.1 * a.2)) =
      ∑ m ∈ realHalfProductSource b N T, F m := by
  classical
  refine Finset.sum_bij (fun a _ => a.1 * a.2) ?_ ?_ ?_ ?_
  · intro a ha
    exact mul_mem_realHalfProductSource ha
  · intro a ha c hc hproduct
    exact realHalfProductPairs_mul_injective ha hc hproduct
  · intro m hm
    obtain ⟨a, ha, _⟩ := realHalfProductSource_existsUnique_pair hm
    exact ⟨a, ha.1, ha.2⟩
  · intro a ha
    rfl

/-- General weighted dictionary, established before specializing any
residue or modulus. It applies to signed real test functions. -/
theorem sum_labelled_W_eq_source (b : ℝ) (N : ℕ) (T : ℝ) (F : ℕ → ℝ) :
    (∑ t ∈ labelledPrimeTuples 2 N, W b N T t * F (labelledProduct t)) =
      ∑ m ∈ realHalfProductSource b N T, F m := by
  classical
  calc
    (∑ t ∈ labelledPrimeTuples 2 N, W b N T t * F (labelledProduct t)) =
        ∑ t ∈ activeCarrier b N T, F (labelledProduct t) := by
      rw [activeCarrier, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro t ht
      by_cases hgeometry : geometry b N T t
      · simp only [W, if_pos hgeometry, one_mul]
      · simp only [W, if_neg hgeometry, zero_mul]
    _ = ∑ a ∈ realHalfProductPairs b N T, F (a.1 * a.2) :=
      sum_activeCarrier_eq_pairs b N T F
    _ = ∑ m ∈ realHalfProductSource b N T, F m :=
      sum_pairs_eq_source b N T F

private theorem sum_source_indicator (b : ℝ) (N : ℕ) (T : ℝ)
    (P : ℕ → Prop) [DecidablePred P] :
    (∑ m ∈ realHalfProductSource b N T, if P m then (1 : ℝ) else 0) =
      (((realHalfProductSource b N T).filter P).card : ℝ) := by
  classical
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- Exact signed Part 3 / physical-error dictionary for the genuine W.
The same Q and rho occur on both sides. No distribution estimate, modulus
positivity, coprimality replacement, evenness, or smoothing licence is assumed. -/
theorem primeProductSignedError_eq_realPhysicalDistributionError
    (b : ℝ) (N : ℕ) (T : ℝ) (Q : Finset ℕ) (rho : ℕ → ℝ) :
    primeProductSignedError 2 N N Q rho (W b N T) =
      realPhysicalDistributionError b N T Q rho := by
  classical
  unfold primeProductSignedError realPhysicalDistributionError
  apply Finset.sum_congr rfl
  intro d hd
  apply congrArg (fun x : ℝ => rho d * x)
  rw [sum_labelled_W_eq_source, Finset.sum_sub_distrib, Finset.sum_div]
  rw [sum_source_indicator, sum_source_indicator]
  rfl

end

end ImbalancedChen.P4BLabelledPairDictionary
