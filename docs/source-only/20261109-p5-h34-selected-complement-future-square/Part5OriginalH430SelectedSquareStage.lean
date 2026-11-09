import Mathlib

/-!
P5.6 / h34 — the LITERAL full-square versus selected-complement-square
support tests in the frozen manuscript's coefficient factorization.

At a new unselected slot j, the manuscript retains both
  S_(j-1) + 2*t_j <= ell_aux
and
  (sum i in I, t_i) + (sum i<j, i not in I, t_i)
      + 2*t_j <= ell_aux.
The selected-complement square includes FUTURE marked slots in I.
It equals the full square only after every selected slot has appeared.
Before then it is stronger whenever those future exponents are positive.

This packet proves the exact future-marked difference and the correct
one-way admission implication. It does NOT identify I with the actual
upper H430 full/selected/inherited count owner, infer the source's
physical Q, or discharge any first-excluded Euler/PP/count obligation.

Pinned toolchain unchanged; SOURCE ONLY / UNCOMPILED / UNEVALUATED.
-/

namespace ImbalancedChen.Part5OriginalH430SelectedSquareStage

noncomputable section
open scoped BigOperators

/-- Manuscript full-square left side: S_(j-1) + 2*t_j, with
zero-based indices and the exact currently inspected slot j. -/
def fullSquareLHS (t : ℕ → ℝ) (j : ℕ) : ℝ :=
  (∑ i ∈ Finset.range j, t i) + 2 * t j

/-- Manuscript selected-complement left side for j not in I.
The FIRST sum is over all marked indices, including marked indices
not yet encountered.  No future slot is silently set to zero. -/
def selectedComplementSquareLHS
    (t : ℕ → ℝ) (I : Finset ℕ) (j : ℕ) : ℝ :=
  (∑ i ∈ I, t i) +
    (∑ i ∈ (Finset.range j) \ I, t i) + 2 * t j

/-- Partition the literal selected index set into past and future.
This is an identity for the actual index set, not a new coefficient. -/
private theorem selected_sum_past_future
    (t : ℕ → ℝ) (I : Finset ℕ) (j : ℕ) :
    (∑ i ∈ I, t i) =
      (∑ i ∈ I ∩ Finset.range j, t i) +
      (∑ i ∈ I \ Finset.range j, t i) := by
  classical
  have hdisj : Disjoint (I ∩ Finset.range j)
      (I \ Finset.range j) := by
    apply Finset.disjoint_left.mpr
    intro i hi hf
    exact (Finset.mem_sdiff.mp hf).2 (Finset.mem_inter.mp hi).2
  have hunion :
      (I ∩ Finset.range j) ∪ (I \ Finset.range j) = I := by
    ext i
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    constructor
    · rintro (⟨hi, _⟩ | ⟨hi, _⟩) <;> exact hi
    · intro hi
      by_cases hp : i ∈ Finset.range j
      · exact Or.inl ⟨hi, hp⟩
      · exact Or.inr ⟨hi, hp⟩
  calc
    _ = ∑ i ∈ (I ∩ Finset.range j) ∪
          (I \ Finset.range j), t i := by rw [hunion]
    _ = _ := Finset.sum_union hdisj

/-- The actual prior full square contains each selected PAST index
and each unselected past index once. -/
private theorem full_sum_selected_and_unselected
    (t : ℕ → ℝ) (I : Finset ℕ) (j : ℕ) :
    (∑ i ∈ Finset.range j, t i) =
      (∑ i ∈ I ∩ Finset.range j, t i) +
      (∑ i ∈ (Finset.range j) \ I, t i) := by
  classical
  have hdisj : Disjoint (I ∩ Finset.range j)
      ((Finset.range j) \ I) := by
    apply Finset.disjoint_left.mpr
    intro i hi hf
    exact (Finset.mem_sdiff.mp hf).2 (Finset.mem_inter.mp hi).1
  have hunion :
      (I ∩ Finset.range j) ∪
        ((Finset.range j) \ I) = Finset.range j := by
    ext i
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    constructor
    · rintro (⟨_, hp⟩ | ⟨hp, _⟩) <;> exact hp
    · intro hp
      by_cases hi : i ∈ I
      · exact Or.inl ⟨hi, hp⟩
      · exact Or.inr ⟨hp, hi⟩
  calc
    _ = ∑ i ∈ (I ∩ Finset.range j) ∪
          ((Finset.range j) \ I), t i := by rw [hunion]
    _ = _ := Finset.sum_union hdisj

/-- The manuscript's selected-complement square equals the FULL
square plus precisely the mass of MARKED SLOTS NOT YET APPEARING.
This correction cannot be deleted before its index set is empty. -/
theorem selected_square_eq_full_plus_future
    (t : ℕ → ℝ) (I : Finset ℕ) (j : ℕ) :
    selectedComplementSquareLHS t I j =
      fullSquareLHS t j +
        (∑ i ∈ I \ Finset.range j, t i) := by
  have hs := selected_sum_past_future t I j
  have hf := full_sum_selected_and_unselected t I j
  unfold selectedComplementSquareLHS fullSquareLHS
  rw [hs, hf]
  ring

/-- Under the ordinary nonnegative logarithmic exponent condition,
the uncompleted selected-complement test is at least as restrictive
as the full-square test.  No root norm or feedback estimate is used. -/
theorem full_square_le_selected_square
    (t : ℕ → ℝ) (I : Finset ℕ) (j : ℕ)
    (ht : ∀ i ∈ I, 0 ≤ t i) :
    fullSquareLHS t j ≤ selectedComplementSquareLHS t I j := by
  have hfuture : 0 ≤ (∑ i ∈ I \ Finset.range j, t i) := by
    apply Finset.sum_nonneg
    intro i hi
    exact ht i (Finset.mem_sdiff.mp hi).1
  rw [selected_square_eq_full_plus_future]
  linarith

/-- Strict future marked mass creates a STRICT extra selected-square
obligation. One cannot replace that gate with the weaker full test. -/
theorem full_square_lt_selected_of_future_positive
    (t : ℕ → ℝ) (I : Finset ℕ) (j : ℕ)
    (hfuture : 0 < ∑ i ∈ I \ Finset.range j, t i) :
    fullSquareLHS t j < selectedComplementSquareLHS t I j := by
  rw [selected_square_eq_full_plus_future]
  linarith

/-- Only once all marked indices are <j does the manuscript's
selected-complement square become the same full-square test. -/
theorem selected_square_eq_full_after_all_marks
    (t : ℕ → ℝ) (I : Finset ℕ) (j : ℕ)
    (hpast : I ⊆ Finset.range j) :
    selectedComplementSquareLHS t I j = fullSquareLHS t j := by
  have hfuture : I \ Finset.range j = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro i hi
    exact (Finset.mem_sdiff.mp hi).2
      (hpast (Finset.mem_sdiff.mp hi).1)
  rw [selected_square_eq_full_plus_future, hfuture]
  simp

/-- A TRUE selected-complement admission at an unselected slot
implies full admission when the selected exponents are nonnegative.
The converse is NOT asserted before all marked slots have appeared. -/
theorem selected_square_admission_implies_full
    (t : ℕ → ℝ) (I : Finset ℕ) (j : ℕ) (ellAux : ℝ)
    (_hj : j ∉ I)
    (ht : ∀ i ∈ I, 0 ≤ t i)
    (hselected : selectedComplementSquareLHS t I j ≤ ellAux) :
    fullSquareLHS t j ≤ ellAux :=
  (full_square_le_selected_square t I j ht).trans hselected

/-- At a post-selection stage, the two complete support tests
are equivalent. Before it, any extra future-selected mass is still
an actual obligation, not an inherited owner assumed to have passed. -/
theorem selected_square_admission_iff_full_after_all_marks
    (t : ℕ → ℝ) (I : Finset ℕ) (j : ℕ) (ellAux : ℝ)
    (hpast : I ⊆ Finset.range j) :
    selectedComplementSquareLHS t I j ≤ ellAux ↔
      fullSquareLHS t j ≤ ellAux := by
  rw [selected_square_eq_full_after_all_marks t I j hpast]

end
end ImbalancedChen.Part5OriginalH430SelectedSquareStage
