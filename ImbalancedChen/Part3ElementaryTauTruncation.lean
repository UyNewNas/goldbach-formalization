import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDivisorMean
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Pi

/-!
SOURCE PROPOSAL ONLY -- 2026-10-22 -- UNCOMPILED -- HOLD

Bounded task: the finite combinatorial core of the elementary short-interval
route, manuscript q1-elementary-shifted-moments-20261010.txt, E1, lines 21-43.
Only this .txt draft and its author checkpoint are delivered. No engineering
Lean file is changed. No compiler, checker, classifier, census, cache or Git
operation is used. No subagent is used by this author. This is heavy0.

Native supplier: goldbach 09b97db5764ade1246bfb77206baa1b124760958.
Mathlib supplier: e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.
Native namespace:
MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry.
Its fouvryTau k is ArithmeticFunction.zeta ^ k; it is NOT a newly defined
pointwise power. Public fouvryTau_succ counts a full divisor convolution.

RESULT DELIVERED HERE:
For any finite indexed set S of natural-valued tuples of common positive
product n, with K = Fintype.card iota >= 2 and n^(K-1) <= D^K, the tuple
cardinality is bounded by the sum, over i and d | n, d <= D, of the cardinal
of the i-deleted fiber of product d. Every remaining coordinate keeps its
original position; deletion is proved injective on the fixed-product set.
Thus repeated numerical factors never collapse distinct ordered tuples.
The outer sum keeps every possible deleted coordinate separately. Ties may
be covered more than once, which is legitimate for the upper bound.

The geometric lemma uses a maximum coordinate. If d is the product of the
other K-1 coordinates, d <= a_i^(K-1), hence
  d^K <= (d*a_i)^(K-1) = n^(K-1) <= D^K,
so d <= D. This is the same elementary finite step as the product of all
K deletion-products argument, with a shorter native API proof.

NOT DELIVERED / PRECISE REMAINING BRIDGE:
The exact desired native theorem is
  forall K n D : Nat, 2 <= K -> 1 <= n -> n^(K-1) <= D^K ->
    fouvryTau K n <=
      K * sum d in n.divisors.filter (fun d => d <= D), fouvryTau (K-1) d.
No such theorem is declared or asserted proved below.

For the explicit all-tuples carrier defined below, the missing general
identity is
  (orderedFactorTuples K n).card = fouvryTau K n.
One must also identify the cardinal of each i-deleted product-d fiber
with the same K-1 ordered tuple count (or bound it by that count).
For the full carrier and d | n, n > 0, this comes from reinserting the
unique deleted coordinate n/d and reindexing the complement of i.
The missing bridge is finite combinatorics, not a mathematical counterexample.
The native recurrence fouvryTau_succ supplies its induction step once the
explicit head/tail product-carrier bijection has been proved. The k=0
base is the empty tuple of product 1. The positive-product restriction
must be kept when canceling or using divisors at zero.

The local existing card_orderedThreeFactors only handles k=3 on a nested
antidiagonal carrier; it does not provide this general identity for Fin K
functions. No unproved tau identity is installed as a hypothesis here.

MATHEMATICAL SCOPE:
This finite step has no primes, congruence condition, high-Omega cutoff,
spectral norm hypothesis, kappa, or weakened main-theorem endpoint. It does
not prove the interval count Y/d+1, harmonic means, E1, E3, Shiu, or any
main theorem / original forall-kappa obligation. Those are outside scope.
All proofs below are complete AS WRITTEN source proposals, not evidence of
Lean elaboration or kernel acceptance. No Lean execution was authorized.
-/

namespace ImbalancedChen.Part3.ElementaryTauTruncation

noncomputable section

open Classical Finset
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Product of all coordinates except the indexed coordinate i. -/
def deletedProduct (a : ι → ℕ) (i : ι) : ℕ :=
  ∏ j ∈ (Finset.univ : Finset ι).erase i, a j

/-- A remaining ordered tuple encoded on the original domain, with i set to 1. -/
def eraseAt (a : ι → ℕ) (i : ι) : ι → ℕ :=
  Function.update a i 1

/-- The actual truncated divisor carrier, with the zero convention of Nat.divisors. -/
def truncatedDivisors (n D : ℕ) : Finset ℕ :=
  n.divisors.filter (fun d => d ≤ D)

/-- No permutation or numerical sorting of the remaining coordinates occurs. -/
def deletionFiber (S : Finset (ι → ℕ)) (i : ι) (d : ℕ) :
    Finset (ι → ℕ) :=
  (S.filter (fun a => deletedProduct a i = d)).image (fun a => eraseAt a i)

theorem deletedProduct_mul (a : ι → ℕ) (i : ι) :
    deletedProduct a i * a i = ∏ j, a j := by
  exact Finset.prod_erase_mul Finset.univ a (Finset.mem_univ i)

theorem deletedProduct_dvd {a : ι → ℕ} {n : ℕ}
    (hprod : (∏ j, a j) = n) (i : ι) : deletedProduct a i ∣ n := by
  exact ⟨a i, ((deletedProduct_mul a i).trans hprod).symm⟩

/-- The cutoff does not require positivity: choosing a maximum also handles zero tuples. -/
theorem exists_deletedProduct_le (a : ι → ℕ) {n D : ℕ}
    (hcard : 2 ≤ Fintype.card ι) (hprod : (∏ j, a j) = n)
    (hcut : n ^ (Fintype.card ι - 1) ≤ D ^ Fintype.card ι) :
    ∃ i : ι, deletedProduct a i ≤ D := by
  have hcpos : 0 < Fintype.card ι := by omega
  have hne : (Finset.univ : Finset ι).Nonempty :=
    Finset.card_pos.mp (by simpa only [Finset.card_univ] using hcpos)
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image Finset.univ a hne
  refine ⟨i, ?_⟩
  have hbound : deletedProduct a i ≤ a i ^ (Fintype.card ι - 1) := by
    simpa only [deletedProduct, Finset.card_erase_of_mem hi, Finset.card_univ] using
      (Finset.prod_le_pow_card ((Finset.univ : Finset ι).erase i) a (a i)
        (fun j _hj => hmax j (Finset.mem_univ j)))
  have hpower : deletedProduct a i ^ Fintype.card ι ≤ n ^ (Fintype.card ι - 1) := by
    calc
      deletedProduct a i ^ Fintype.card ι =
          deletedProduct a i ^ ((Fintype.card ι - 1) + 1) := by
            congr 1
            omega
      _ = deletedProduct a i ^ (Fintype.card ι - 1) * deletedProduct a i :=
        pow_succ _ _
      _ ≤ deletedProduct a i ^ (Fintype.card ι - 1) * a i ^ (Fintype.card ι - 1) :=
        Nat.mul_le_mul_left _ hbound
      _ = (deletedProduct a i * a i) ^ (Fintype.card ι - 1) := (mul_pow _ _ _).symm
      _ = n ^ (Fintype.card ι - 1) := by rw [deletedProduct_mul, hprod]
  exact le_of_pow_le_pow_left₀ (by omega) (Nat.zero_le D) (hpower.trans hcut)

/-- At a fixed positive total product, a deleted coordinate is uniquely recoverable. -/
theorem eraseAt_injective_of_product {a b : ι → ℕ} {n : ℕ}
    (hn : 0 < n) (ha : (∏ j, a j) = n) (hb : (∏ j, b j) = n)
    (i : ι) (hab : eraseAt a i = eraseAt b i) : a = b := by
  have hdel : deletedProduct a i = deletedProduct b i := by
    apply Finset.prod_congr rfl
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    have heval := congrFun hab j
    simpa only [eraseAt, Function.update_of_ne hji] using heval
  have hnonzero : deletedProduct a i ≠ 0 := by
    intro hz
    have hp : deletedProduct a i * a i = n := (deletedProduct_mul a i).trans ha
    rw [hz, zero_mul] at hp
    exact hn.ne' hp.symm
  have hai : a i = b i := by
    apply mul_left_cancel₀ hnonzero
    calc
      deletedProduct a i * a i = n := (deletedProduct_mul a i).trans ha
      _ = deletedProduct b i * b i := ((deletedProduct_mul b i).trans hb).symm
      _ = deletedProduct a i * b i := by rw [hdel]
  funext j
  by_cases hji : j = i
  · subst j
    exact hai
  · have heval := congrFun hab j
    simpa only [eraseAt, Function.update_of_ne hji] using heval

/-- The indexed cover pays every possible deletion position once in its sum. -/
theorem card_le_sum_smallCovers (S : Finset (ι → ℕ)) {n D : ℕ}
    (hcard : 2 ≤ Fintype.card ι) (hprod : ∀ a ∈ S, (∏ j, a j) = n)
    (hcut : n ^ (Fintype.card ι - 1) ≤ D ^ Fintype.card ι) :
    S.card ≤ ∑ i : ι, (S.filter (fun a => deletedProduct a i ≤ D)).card := by
  have hcover : S ⊆ (Finset.univ : Finset ι).biUnion
      (fun i => S.filter (fun a => deletedProduct a i ≤ D)) := by
    intro a ha
    obtain ⟨i, hi⟩ := exists_deletedProduct_le a hcard (hprod a ha) hcut
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, Finset.mem_filter.mpr ⟨ha, hi⟩⟩
  exact (Finset.card_le_card hcover).trans Finset.card_biUnion_le

/-- Exact finite divisor-fiber truncation, retaining all ordered multiplicities. -/
theorem card_le_sum_deletionFibers (S : Finset (ι → ℕ)) {n D : ℕ}
    (hn : 0 < n) (hcard : 2 ≤ Fintype.card ι)
    (hprod : ∀ a ∈ S, (∏ j, a j) = n)
    (hcut : n ^ (Fintype.card ι - 1) ≤ D ^ Fintype.card ι) :
    S.card ≤ ∑ i : ι, ∑ d ∈ truncatedDivisors n D, (deletionFiber S i d).card := by
  calc
    S.card ≤ ∑ i : ι, (S.filter (fun a => deletedProduct a i ≤ D)).card :=
      card_le_sum_smallCovers S hcard hprod hcut
    _ = ∑ i : ι, ∑ d ∈ truncatedDivisors n D, (deletionFiber S i d).card := by
      apply Finset.sum_congr rfl
      intro i _hi
      have hmaps : Set.MapsTo (fun a => deletedProduct a i)
          (S.filter (fun a => deletedProduct a i ≤ D)) (truncatedDivisors n D) := by
        intro a ha
        obtain ⟨haS, haD⟩ := Finset.mem_filter.mp ha
        exact Finset.mem_filter.mpr
          ⟨Nat.mem_divisors.mpr ⟨deletedProduct_dvd (hprod a haS) i, hn.ne'⟩, haD⟩
      rw [Finset.card_eq_sum_card_fiberwise (f := fun a => deletedProduct a i)
        (s := S.filter (fun a => deletedProduct a i ≤ D))
        (t := truncatedDivisors n D) hmaps]
      apply Finset.sum_congr rfl
      intro d hd
      have hdD : d ≤ D := (Finset.mem_filter.mp hd).2
      have hfiber :
          ((S.filter (fun a => deletedProduct a i ≤ D)).filter
            (fun a => deletedProduct a i = d)) =
          S.filter (fun a => deletedProduct a i = d) := by
        ext a
        simp only [Finset.mem_filter]
        constructor
        · intro ha
          exact ⟨ha.1.1, ha.2⟩
        · rintro ⟨haS, had⟩
          exact ⟨⟨haS, had.le.trans hdD⟩, had⟩
      rw [hfiber]
      unfold deletionFiber
      symm
      apply Finset.card_image_of_injOn
      intro a ha b hb hab
      exact eraseAt_injective_of_product hn
        (hprod a (Finset.mem_filter.mp ha).1)
        (hprod b (Finset.mem_filter.mp hb).1) i hab

/-- An explicit finite carrier of all ordered positive k-factorizations when n > 0. -/
def orderedFactorTuples (k n : ℕ) : Finset (Fin k → ℕ) :=
  (Fintype.piFinset (fun _ : Fin k => n.divisors)).filter (fun a => (∏ j, a j) = n)

/-- Specialization to the actual all-factor-tuples carrier, still without a tau identity. -/
theorem card_orderedFactorTuples_truncated {K n D : ℕ}
    (hK : 2 ≤ K) (hn : 1 ≤ n) (hcut : n ^ (K - 1) ≤ D ^ K) :
    (orderedFactorTuples K n).card ≤
      ∑ i : Fin K, ∑ d ∈ truncatedDivisors n D,
        (deletionFiber (orderedFactorTuples K n) i d).card := by
  apply card_le_sum_deletionFibers (hn := by omega)
  · simpa only [Fintype.card_fin] using hK
  · intro a ha
    exact (Finset.mem_filter.mp ha).2
  · simpa only [Fintype.card_fin] using hcut

end

end ImbalancedChen.Part3.ElementaryTauTruncation
