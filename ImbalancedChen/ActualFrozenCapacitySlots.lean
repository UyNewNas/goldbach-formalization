import ImbalancedChen.ActualPrimeTupleNormalization
import Mathlib.Data.List.FinRange

/-!
# A single endpoint allocation for every tuple of an original prime box

The greedy algorithm runs on the upper weights of the original labelled
slots once.  Natural factors for every actual tuple use those same two
lists of slot labels.  Bounds and the original product identity are proved
for all coordinatewise smaller tuples, without rerunning their decisions.
This auxiliary allocation need not agree with the earlier tuplewise greedy.

The support premise is the full original upper vector, not a caller-chosen
allocation.  For a selected pair its original remaining vector must first
be derived from the original full support by the concrete selected-mask
dictionary.  A separate endpoint-inflation lemma pays upper support from
the original source vector.  No distribution assertion is made here.
-/

namespace ImbalancedChen

noncomputable section

open MathlibNt.SieveTheory.LiLiuPrereqWFBoxAllocation
open scoped Classical BigOperators

private theorem prefixSquareBound_map {α : Type*} (upper : α → ℕ)
    (D : ℝ) (input : List α)
    (hfull : actualDwellSupport D (input.map upper)) :
    PrefixSquareBound (fun i => (upper i : ℝ)) D input := by
  intro i hi
  have h := hfull i (by simpa only [List.length_map] using hi)
  simpa only [← List.map_take, List.map_map, List.getElem_map, Function.comp_def] using h

/-- Mapping slot labels after the run gives exactly the run on their
upper values. Repeated upper values do not merge their original slots. -/
theorem actualTwoCapacityGreedy_map {α β : Type*} (f : α → β) (weight : β → ℝ)
    (A : ℝ) (input : List α) :
    actualTwoCapacityGreedy weight A (input.map f) =
      ((actualTwoCapacityGreedy (fun i => weight (f i)) A input).1.map f,
        (actualTwoCapacityGreedy (fun i => weight (f i)) A input).2.map f) := by
  induction input using List.reverseRecOn with
  | nil => simp [actualTwoCapacityGreedy]
  | append_singleton input p ih =>
      rw [List.map_append, List.map_singleton,
        actualTwoCapacityGreedy_append, actualTwoCapacityGreedy_append, ih]
      unfold actualTwoCapacityStep
      simp only [List.map_map, Function.comp_def]
      split_ifs <;> simp only [List.map_append, List.map_singleton]

/-- The bin labels depend only on upper, A, and the original slot list. -/
def actualFrozenCapacityFactors {α : Type*} (A : ℝ) (upper actual : α → ℕ)
    (input : List α) : ℕ × ℕ :=
  (((actualTwoCapacityGreedy (fun i => (upper i : ℝ)) A input).1.map actual).prod,
    ((actualTwoCapacityGreedy (fun i => (upper i : ℝ)) A input).2.map actual).prod)

theorem actualFrozenCapacityFactors_at_upper {α : Type*} (A : ℝ) (upper : α → ℕ)
    (input : List α) :
    actualFrozenCapacityFactors A upper upper input =
      actualTwoCapacityFactors A (input.map upper) := by
  unfold actualFrozenCapacityFactors actualTwoCapacityFactors
  rw [actualTwoCapacityGreedy_map]

private theorem mapped_prod_le_upper_prod {α : Type*} (upper actual : α → ℕ)
    (input : List α) (hsize : ∀ i ∈ input, actual i ≤ upper i) :
    (((input.map actual).prod : ℕ) : ℝ) ≤ (input.map (fun i => (upper i : ℝ))).prod := by
  rw [← actualNatList_cast_prod (input.map actual)]
  simpa only [List.map_map, Function.comp_def] using
    (List.prod_map_le_prod_map₀ (fun i => (actual i : ℝ)) (fun i => (upper i : ℝ))
      (fun i _ => Nat.cast_nonneg _) (fun i hi => by exact_mod_cast hsize i hi))

/-- The same computed slot lists work for every actual tuple under the
upper vector. No assignment or factors are supplied by the caller. -/
theorem actualFrozenCapacityFactors_correct {α : Type*} {A B : ℝ}
    (hA : 1 ≤ A) (hB : 1 ≤ B) (upper actual : α → ℕ) (input : List α)
    (hfull : actualDwellSupport (A * B) (input.map upper))
    (hsize : ∀ i ∈ input, actual i ≤ upper i) :
    (actualFrozenCapacityFactors A upper actual input).1 *
        (actualFrozenCapacityFactors A upper actual input).2 = (input.map actual).prod ∧
      ((actualFrozenCapacityFactors A upper actual input).1 : ℝ) ≤ A ∧
      ((actualFrozenCapacityFactors A upper actual input).2 : ℝ) ≤ B := by
  obtain ⟨hpart, hleft, hright⟩ := actualTwoCapacityGreedy_correct
    (fun i => (upper i : ℝ)) hA hB input (prefixSquareBound_map upper _ input hfull)
  refine ⟨?_, ?_, ?_⟩
  · have h := (hpart.perm.map actual).prod_eq
    simpa only [List.map_append, List.prod_append, actualFrozenCapacityFactors] using h
  · exact (mapped_prod_le_upper_prod upper actual _
      (fun i hi => hsize i (hpart.sublists.1.subset hi))).trans hleft
  · exact (mapped_prod_le_upper_prod upper actual _
      (fun i hi => hsize i (hpart.sublists.2.subset hi))).trans hright

/-- Actual original distinct primes, together with the just-proved product
identity, pay coprimality for this fixed endpoint allocation as well. -/
theorem actualFrozenCapacityFactors_coprime {α : Type*} {A B : ℝ}
    (hA : 1 ≤ A) (hB : 1 ≤ B) (upper actual : α → ℕ) (input : List α)
    (hfull : actualDwellSupport (A * B) (input.map upper))
    (hsize : ∀ i ∈ input, actual i ≤ upper i)
    (hprime : ∀ p ∈ input.map actual, Nat.Prime p) (hnodup : (input.map actual).Nodup) :
    Nat.Coprime (actualFrozenCapacityFactors A upper actual input).1
      (actualFrozenCapacityFactors A upper actual input).2 := by
  have hprod := (actualFrozenCapacityFactors_correct hA hB upper actual input hfull hsize).1
  have hs := actualPrimeVector_squarefree (input.map actual) hprime hnodup
  rw [← hprod] at hs
  exact Nat.coprime_of_squarefree_mul hs

/-- Every member of the original coordinate box receives these same slot
lists. The empty vector and equal upper endpoints are included. -/
theorem actualFrozenCapacityFactors_on_box {n : ℕ} {A B : ℝ}
    (hA : 1 ≤ A) (hB : 1 ≤ B) (upper : Fin n → ℕ)
    (hfull : actualDwellSupport (A * B) (List.ofFn upper)) :
    ∀ actual : Fin n → ℕ, (∀ i, actual i ≤ upper i) →
      (actualFrozenCapacityFactors A upper actual (List.finRange n)).1 *
          (actualFrozenCapacityFactors A upper actual (List.finRange n)).2 =
          (List.ofFn actual).prod ∧
        ((actualFrozenCapacityFactors A upper actual (List.finRange n)).1 : ℝ) ≤ A ∧
        ((actualFrozenCapacityFactors A upper actual (List.finRange n)).2 : ℝ) ≤ B := by
  intro actual hsize
  simpa only [← List.ofFn_eq_map] using
    actualFrozenCapacityFactors_correct hA hB upper actual (List.finRange n)
      (by simpa only [← List.ofFn_eq_map] using hfull) (fun i _ => hsize i)

/-- A finite assignment label for a whole upper-endpoint box, rather than
for individual tuples selected inside it. -/
def actualFrozenCapacityAssignment {n : ℕ} (A : ℝ) (upper : Fin n → ℕ) : Fin n → Bool :=
  fun i => decide (i ∈ (actualTwoCapacityGreedy (fun i => (upper i : ℝ)) A (List.finRange n)).1)

theorem actualFrozenCapacityAssignment_card (n : ℕ) :
    Fintype.card (Fin n → Bool) = 2 ^ n := by simp

/-- Partition the original finite box family by its computed slot word.
Every signed scalar is retained in this exact identity. Individual boxes
remain intact; no tuple fibre is asserted to be a rectangular box. -/
theorem actualFrozenCapacityAssignment_sum_partition {ι M : Type*}
    [DecidableEq ι] [AddCommMonoid M] {n : ℕ} (J : Finset ι)
    (A : ℝ) (upper : ι → Fin n → ℕ) (F : ι → M) :
    (∑ mask : Fin n → Bool,
      ∑ j ∈ J.filter (fun j => actualFrozenCapacityAssignment A (upper j) = mask), F j) =
      ∑ j ∈ J, F j := by
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

end

end ImbalancedChen
