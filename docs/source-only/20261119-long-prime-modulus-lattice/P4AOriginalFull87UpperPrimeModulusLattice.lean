import ImbalancedChen.P4AOriginalFull87UpperPrimeWindowWidth
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

Improve the previous upper-half LONG Rosser prime-window invoice by
retaining the ORIGINAL full modulus b = (p :: pre).prod. A nonzero
prime fibre forces b | (N-P), not just N-X*p <= P < (N+1)/2.

The new finite invoice counts only points in that literal modulus
lattice inside the prior interval. It is <= the old interval-width
invoice, and can be dramatically smaller when b is large.

No new prime distribution hypothesis, no smoothing, no new physical
rho, and no replacement of actual beta or original fifth/sixth events.
The Rosser quotient and every occurrence remain unchanged in the sum.
-/

namespace ImbalancedChen.P4AOriginalFull87UpperPrimeModulusLattice
noncomputable section
open scoped Classical BigOperators

open P4AOriginalFull87UpperPrimeWindowWidth
  (longPrimeWindow original_long_fibre_abs_le_one
   long_fibre_nonzero_in_prime_window)
open P4AOriginalFull87UpperPrimeShortBoundary
  (upperPrimeLongBoundaryTerm)
open P4AOriginalFull87StoppedGlobalPrimeLedger
  (upperPrimeFibreTerm)
open P4AOriginalFull87FirstFifthStoppedEvents
  (FifthStoppedEvent)

/-- The actual complete sixth modulus supplies a congruence restriction
on the same original prime window. This is ONLY an upper-bound carrier;
it is not used in the definition of the original prime fibre. -/
def longPrimeModulusWindow
    (N X : ℕ) (pre : List ℕ) (p : ℕ) : Finset ℕ :=
  (longPrimeWindow N X p).filter
    (fun P => (p :: pre).prod ∣ N - P)

/-- A nonzero original LONG fibre forces exact divisibility by the
full six-prime modulus, with the existing Rosser quotient. No replacement
prime set or extra mask is applied to the original summand. -/
theorem long_fibre_nonzero_full_modulus_dvd
    (N cap : ℕ) (w L : ℝ) (X P : ℕ)
    (pre : List ℕ) (p : ℕ)
    (h : upperPrimeLongBoundaryTerm
      N cap w L X P pre p ≠ 0) :
    (p :: pre).prod ∣ N - P := by
  have hs : ¬ X * p < N - P := by
    intro hshort
    apply h
    simp [upperPrimeLongBoundaryTerm, hshort]
  have hbase : upperPrimeFibreTerm
      N cap w L X P pre p ≠ 0 := by
    simpa only [upperPrimeLongBoundaryTerm, if_neg hs] using h
  have hmul :
      ((N - P) / (p :: pre).prod) * (p :: pre).prod = N - P := by
    by_contra hnot
    apply hbase
    simp [upperPrimeFibreTerm, hnot]
  exact ⟨(N - P) / (p :: pre).prod,
    by simpa only [mul_comm] using hmul.symm⟩

/-- Every nonzero old upper-half LONG fibre belongs to the smaller
integer lattice, with both strict original window boundaries intact. -/
theorem long_fibre_nonzero_in_modulus_window
    (N cap : ℕ) (w L : ℝ) (X P : ℕ)
    (pre : List ℕ) (p : ℕ)
    (h : upperPrimeLongBoundaryTerm
      N cap w L X P pre p ≠ 0) :
    P ∈ longPrimeModulusWindow N X pre p := by
  apply Finset.mem_filter.mpr
  exact ⟨long_fibre_nonzero_in_prime_window
      N cap w L X P pre p h,
    long_fibre_nonzero_full_modulus_dvd
      N cap w L X P pre p h⟩

private theorem finite_sum_abs_le_sum_abs
    (S : Finset ℕ) (f : ℕ → ℝ) :
    |∑ P ∈ S, f P| ≤ ∑ P ∈ S, |f P| := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert x S hx ih =>
      simp only [Finset.sum_insert hx]
      exact (abs_add_le (f x) (∑ P ∈ S, f P)).trans
        (add_le_add_left ih _)

/-- A stronger finite invoice: count only genuine lattice points
allowed by the same six-prime complete modulus. The ORIGINAL long
Rosser term, beta, quotient and all its zeros are left untouched.
No prime-counting statement has been inserted. -/
theorem original_long_prime_sum_abs_le_modulus_card
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (pre : List ℕ) (p : ℕ) :
    |∑ P ∈ chenPrimePrefix N,
        upperPrimeLongBoundaryTerm N cap w L X P pre p| ≤
      ((longPrimeModulusWindow N X pre p).card : ℝ) := by
  classical
  let W := longPrimeModulusWindow N X pre p
  have hsupport :
      (∑ P ∈ chenPrimePrefix N,
        |upperPrimeLongBoundaryTerm N cap w L X P pre p|) =
      ∑ P ∈ (chenPrimePrefix N).filter (fun P => P ∈ W),
        |upperPrimeLongBoundaryTerm N cap w L X P pre p| := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro P hP
    by_cases hpW : P ∈ W
    · simp [hpW]
    · have hz :
        upperPrimeLongBoundaryTerm N cap w L X P pre p = 0 := by
        by_contra hnon
        exact hpW (long_fibre_nonzero_in_modulus_window
          N cap w L X P pre p hnon)
      simp [hpW, hz]
  have hterms :
      (∑ P ∈ (chenPrimePrefix N).filter (fun P => P ∈ W),
        |upperPrimeLongBoundaryTerm N cap w L X P pre p|) ≤
      ∑ P ∈ (chenPrimePrefix N).filter (fun P => P ∈ W),
        (1 : ℝ) := by
    apply Finset.sum_le_sum
    intro P hp
    exact original_long_fibre_abs_le_one N cap w L X P pre p
  have hsubset :
      (chenPrimePrefix N).filter (fun P => P ∈ W) ⊆ W := by
    intro P hP
    exact (Finset.mem_filter.mp hP).2
  calc
    |∑ P ∈ chenPrimePrefix N,
        upperPrimeLongBoundaryTerm N cap w L X P pre p|
        ≤ ∑ P ∈ chenPrimePrefix N,
          |upperPrimeLongBoundaryTerm N cap w L X P pre p| :=
            finite_sum_abs_le_sum_abs _ _
    _ = ∑ P ∈ (chenPrimePrefix N).filter (fun P => P ∈ W),
          |upperPrimeLongBoundaryTerm N cap w L X P pre p| := hsupport
    _ ≤ ∑ P ∈ (chenPrimePrefix N).filter (fun P => P ∈ W),
          (1 : ℝ) := hterms
    _ = (((chenPrimePrefix N).filter (fun P => P ∈ W)).card : ℝ) := by
          simp
    _ ≤ (W.card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsubset

/-- The lattice invoice is always no worse than the previous integer
window; the old payment must be REPLACED, never added a second time. -/
theorem modulus_window_card_le_old_window
    (N X : ℕ) (pre : List ℕ) (p : ℕ) :
    (longPrimeModulusWindow N X pre p).card ≤
      (longPrimeWindow N X p).card := by
  apply Finset.card_le_card
  intro P hP
  exact (Finset.mem_filter.mp hP).1

private theorem prime_list_swap {α : Type*}
    (xs : List α) (S : Finset ℕ) (f : α → ℕ → ℝ) :
    (∑ P ∈ S, (xs.map (fun x => f x P)).sum) =
    (xs.map (fun x => ∑ P ∈ S, f x P)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib]
      rw [ih]

private theorem list_sum_abs_le_bounds {α : Type*}
    (xs : List α) (f g : α → ℝ)
    (hg : ∀ x ∈ xs, |f x| ≤ g x) :
    |(xs.map f).sum| ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx : |f x| ≤ g x := hg x (by simp)
      have ht : ∀ y ∈ xs, |f y| ≤ g y := by
        intro y hy
        exact hg y (by simp [hy])
      simp only [List.map_cons, List.sum_cons]
      exact (abs_add_le (f x) (xs.map f).sum).trans
        (add_le_add hx (ih ht))

/-- Replace the previous positive-part width invoice on the SAME
ordered original sixth occurrences by the tighter complete-modulus
lattice invoice. Exact fifth signed mass is retained; a repeated sixth
occurrence remains repeated and incurs its own physical charge once. -/
theorem original_fifth_ordered_long_prime_modulus_budget
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (fifth : FifthStoppedEvent ℕ) :
    |∑ P ∈ chenPrimePrefix N,
      (fifth.remainingAfter.map (fun p =>
        signedTreeCoefficient true fifth.massAfter *
          upperPrimeLongBoundaryTerm N cap w L X P
            fifth.selectedAfter p)).sum| ≤
      (fifth.remainingAfter.map (fun p =>
        |signedTreeCoefficient true fifth.massAfter| *
          ((longPrimeModulusWindow N X fifth.selectedAfter p).card : ℝ))).sum := by
  rw [prime_list_swap fifth.remainingAfter (chenPrimePrefix N)
    (fun p P =>
      signedTreeCoefficient true fifth.massAfter *
        upperPrimeLongBoundaryTerm N cap w L X P fifth.selectedAfter p)]
  apply list_sum_abs_le_bounds
  intro p hp
  rw [← Finset.mul_sum, abs_mul]
  exact mul_le_mul_of_nonneg_left
    (original_long_prime_sum_abs_le_modulus_card
      N cap w L X fifth.selectedAfter p)
    (abs_nonneg _)

end
end ImbalancedChen.P4AOriginalFull87UpperPrimeModulusLattice
