import ImbalancedChen.P4AOriginalFull87UpperPrimeLiveZWindow
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

An explicit *finite quantitative* invoice for the SAME original
upper-half LONG Rosser prime fibre.  The previous local-window proof
gave NONZERO => N - X*p <= P and 2*P<N, but did not price the number of
admissible P.  Here each complete-beta term is <= 1 in absolute value
(using the pinned actualSmallRosserPlus_abs_le_one), and the original
prime prefix can meet that window at most

    ((N+1)/2 - (N-X*p))_+

times; for even N this is <= (X*p - N/2)_+.

The exact original Rosser quotient and fifth-power gate are NOT erased
from the LONG term.  All prime-fibre signs and repeated ordered sixth
occurrences survive the final per-fifth signed bound.

This is a genuine finite, possibly huge, upper bound.  No claim that it
is o(H_N), no smooth PP call, no target-equivalent assumption.
-/

namespace ImbalancedChen.P4AOriginalFull87UpperPrimeWindowWidth
noncomputable section
open scoped Classical BigOperators

open P4AOriginalFull87UpperPrimeShortBoundary
  (upperPrimeLongBoundaryTerm)
open P4AOriginalFull87UpperPrimeLiveZWindow
  (long_fibre_nonzero_prime_window)
open P4AOriginalFull87FirstFifthStoppedEvents
  (FifthStoppedEvent)

/-- Integer interval that contains EVERY nonzero original LONG
fibre, with precisely the upper-half *strict* endpoint.  This is a
bounding carrier only; it does not replace the original term mask. -/
def longPrimeWindow (N X p : ℕ) : Finset ℕ :=
  Finset.Ico (N - X * p) ((N + 1) / 2)

/-- The previous original nonzero witness gives both endpoints of
the integer interval, preserving the strict 2*P<N condition. -/
theorem long_fibre_nonzero_in_prime_window
    (N cap : ℕ) (w L : ℝ) (X P : ℕ)
    (pre : List ℕ) (p : ℕ)
    (h : upperPrimeLongBoundaryTerm N cap w L X P pre p ≠ 0) :
    P ∈ longPrimeWindow N X p := by
  obtain ⟨hhalf, hlow, _, _⟩ :=
    long_fibre_nonzero_prime_window N cap w L X P pre p h
  exact Finset.mem_Ico.mpr ⟨hlow, by omega⟩

/-- Uniform coefficient size for the ORIGINAL plus-beta fibre.  It
uses the real pinned Rosser coefficient lemma, rather than an invented
bound on an arbitrary replacement coefficient. -/
theorem original_long_fibre_abs_le_one
    (N cap : ℕ) (w L : ℝ) (X P : ℕ)
    (pre : List ℕ) (p : ℕ) :
    |upperPrimeLongBoundaryTerm N cap w L X P pre p| ≤ 1 := by
  by_cases hs : X * p < N - P
  · simp [upperPrimeLongBoundaryTerm, hs]
  · simp only [upperPrimeLongBoundaryTerm, if_neg hs]
    unfold P4AOriginalFull87StoppedGlobalPrimeLedger.upperPrimeFibreTerm
    split_ifs with hg
    · exact actualSmallRosserPlus_abs_le_one
        N cap w L ((N - P) / (p :: pre).prod)
    · simp

/-- For even targets the exact window length is at most the excess
of X*p over N/2. Nat subtraction retains the positive part and also
handles X*p>N without introducing a negative lower endpoint. -/
theorem even_long_window_card_le_excess
    (N X p : ℕ) (hEven : Even N) :
    (longPrimeWindow N X p).card ≤ X * p - N / 2 := by
  have hc : (longPrimeWindow N X p).card =
      (N + 1) / 2 - (N - X * p) := by
    simp [longPrimeWindow]
  rw [hc]
  obtain ⟨k, hk⟩ := hEven
  omega

/-- Local triangle inequality, proved at the finite-set level; the
prime count is never inferred from an analytic prime theorem. -/
private theorem finite_abs_sum_le_sum_abs
    (S : Finset ℕ) (f : ℕ → ℝ) :
    |∑ P ∈ S, f P| ≤ ∑ P ∈ S, |f P| := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert x S hx ih =>
      simp only [Finset.sum_insert hx]
      exact (abs_add_le (f x) (∑ P ∈ S, f P)).trans
        (add_le_add_left ih _)

/-- The FULL original upper-half long Rosser prime sum is bounded by
the cardinality of its exact arithmetical window.  Original beta,
integer quotient, high-q filter, strict endpoints and all zeros
remain inside upperPrimeLongBoundaryTerm. -/
theorem original_long_prime_sum_abs_le_window_card
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (pre : List ℕ) (p : ℕ) :
    |∑ P ∈ chenPrimePrefix N,
        upperPrimeLongBoundaryTerm N cap w L X P pre p| ≤
      ((longPrimeWindow N X p).card : ℝ) := by
  classical
  let W := longPrimeWindow N X p
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
        by_contra hn
        exact hpW (long_fibre_nonzero_in_prime_window
          N cap w L X P pre p hn)
      simp [hpW, hz]
  have hterm :
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
          finite_abs_sum_le_sum_abs _ _
    _ = ∑ P ∈ (chenPrimePrefix N).filter (fun P => P ∈ W),
          |upperPrimeLongBoundaryTerm N cap w L X P pre p| := hsupport
    _ ≤ ∑ P ∈ (chenPrimePrefix N).filter (fun P => P ∈ W),
          (1 : ℝ) := hterm
    _ = (((chenPrimePrefix N).filter (fun P => P ∈ W)).card : ℝ) := by simp
    _ ≤ (W.card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsubset

/-- Fully explicit even-target price for a single actual sixth
occurrence.  This is arithmetic, NOT a new H_N asymptotic. -/
theorem original_long_prime_sum_abs_le_excess
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (pre : List ℕ) (p : ℕ) (hEven : Even N) :
    |∑ P ∈ chenPrimePrefix N,
        upperPrimeLongBoundaryTerm N cap w L X P pre p| ≤
      ((X * p - N / 2 : ℕ) : ℝ) := by
  calc
    _ ≤ ((longPrimeWindow N X p).card : ℝ) :=
      original_long_prime_sum_abs_le_window_card N cap w L X pre p
    _ ≤ ((X * p - N / 2 : ℕ) : ℝ) := by
      exact_mod_cast even_long_window_card_le_excess N X p hEven

/-- Literal signed fifth mass multiplies the SAME Rosser prime fibre,
so its absolute payment is the original mass times the arithmetic
positive-part window. -/
theorem original_signed_long_prime_sum_abs_le_excess
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (pre : List ℕ) (p : ℕ) (mass : ℝ)
    (hEven : Even N) :
    |∑ P ∈ chenPrimePrefix N,
        mass * upperPrimeLongBoundaryTerm N cap w L X P pre p| ≤
      |mass| * ((X * p - N / 2 : ℕ) : ℝ) := by
  rw [← Finset.mul_sum, abs_mul]
  exact mul_le_mul_of_nonneg_left
    (original_long_prime_sum_abs_le_excess
      N cap w L X pre p hEven) (abs_nonneg mass)

/-- Finite interchange keeps every occurrence in the actual sixth
List, without List.toFinset or any change to its Rosser quotient. -/
private theorem prime_list_swap {α : Type*}
    (xs : List α) (S : Finset ℕ) (f : α → ℕ → ℝ) :
    (∑ P ∈ S, (xs.map (fun x => f x P)).sum) =
    (xs.map (fun x => ∑ P ∈ S, f x P)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib]
      rw [ih]

private theorem list_sum_abs_le_sum_bounds {α : Type*}
    (xs : List α) (f b : α → ℝ)
    (hb : ∀ x ∈ xs, |f x| ≤ b x) :
    |(xs.map f).sum| ≤ (xs.map b).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx : |f x| ≤ b x := hb x (by simp)
      have htail : ∀ y ∈ xs, |f y| ≤ b y := by
        intro y hy
        exact hb y (by simp [hy])
      simp only [List.map_cons, List.sum_cons]
      exact (abs_add_le (f x) (xs.map f).sum).trans
        (add_le_add hx (ih htail))

/-- The exact fifth mass and *ordered* sixth occurrences receive one
finite integer-width budget, after summing the very same prime prefix.
No saved87 geometric or asymptotic result is smuggled into the price.
This theorem is available for genuine fifthExclusive events without
altering the source, even though no global producer-X bound is known. -/
theorem original_fifth_ordered_long_prime_budget
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (fifth : FifthStoppedEvent ℕ) (hEven : Even N) :
    |∑ P ∈ chenPrimePrefix N,
      (fifth.remainingAfter.map (fun p =>
        signedTreeCoefficient true fifth.massAfter *
          upperPrimeLongBoundaryTerm N cap w L X P
            fifth.selectedAfter p)).sum| ≤
      (fifth.remainingAfter.map (fun p =>
        |signedTreeCoefficient true fifth.massAfter| *
          ((X * p - N / 2 : ℕ) : ℝ))).sum := by
  rw [prime_list_swap fifth.remainingAfter (chenPrimePrefix N)
    (fun p P =>
      signedTreeCoefficient true fifth.massAfter *
        upperPrimeLongBoundaryTerm N cap w L X P fifth.selectedAfter p)]
  apply list_sum_abs_le_sum_bounds
  intro p hp
  exact original_signed_long_prime_sum_abs_le_excess
    N cap w L X fifth.selectedAfter p
    (signedTreeCoefficient true fifth.massAfter) hEven

end
end ImbalancedChen.P4AOriginalFull87UpperPrimeWindowWidth
