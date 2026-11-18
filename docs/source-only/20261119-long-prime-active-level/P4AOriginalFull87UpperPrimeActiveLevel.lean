import ImbalancedChen.P4AOriginalFull87UpperPrimeModulusLattice
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

Strengthen the SAME original upper-half LONG prime-fibre invoice using
the actual strict Rosser level. Nonzero beta on the original complete
quotient a = (N-P)/b forces a < L and a in the genuine small Rosser
support. Combined with b | N-P and 2*P<N, this forces N < 2*L*b.

The new finite carrier is a strict subset of the previous complete-
modulus lattice, not a newly attached filter on the original term.
The previous lattice invoice is REPLACED, not paid twice. No smooth PP,
prime distribution, independent producer-bound premise or new rho.
-/

namespace ImbalancedChen.P4AOriginalFull87UpperPrimeActiveLevel
noncomputable section
open scoped Classical BigOperators

open P4AOriginalFull87UpperPrimeShortBoundary
  (upperPrimeLongBoundaryTerm)
open P4AOriginalFull87StoppedGlobalPrimeLedger
  (upperPrimeFibreTerm)
open P4AOriginalFull87UpperPrimeWindowWidth
  (original_long_fibre_abs_le_one)
open P4AOriginalFull87UpperPrimeModulusLattice
  (longPrimeModulusWindow long_fibre_nonzero_full_modulus_dvd
   long_fibre_nonzero_in_modulus_window)
open P4AOriginalFull87UpperPrimeLiveZWindow
  (long_fibre_nonzero_prime_window)
open P4AOriginalFull87FirstFifthStoppedEvents
  (FifthStoppedEvent)

/-- Nonzero of the ORIGINAL long fibre forces the actual upper Rosser
coefficient to be active. This uses the pinned weight provider, not a
hypothesis that an arbitrary replacement coefficient is nonzero. -/
theorem long_fibre_nonzero_active_rosser
    (N cap : ℕ) (w L : ℝ) (X P : ℕ)
    (pre : List ℕ) (p : ℕ)
    (h : upperPrimeLongBoundaryTerm
      N cap w L X P pre p ≠ 0) :
    let a := (N - P) / (p :: pre).prod
    a ∈ actualSmallRosserSupport N cap w ∧ (a : ℝ) < L := by
  have hs : ¬ X * p < N - P := by
    intro hshort
    apply h
    simp [upperPrimeLongBoundaryTerm, hshort]
  have hf : upperPrimeFibreTerm N cap w L X P pre p ≠ 0 := by
    simpa only [upperPrimeLongBoundaryTerm, if_neg hs] using h
  unfold upperPrimeFibreTerm at hf
  split_ifs at hf with hg
  · exact ⟨(actualSmallRosserPlus_active hf).1,
      (actualSmallRosserPlus_active hf).2.1⟩
  · contradiction

/-- Original full q=a*b, strict upper-half, and strict active Rosser
level imply a literal *physical-size* necessary condition. The factor
b is the complete six-prime modulus, not just the sixth prime p. -/
theorem long_fibre_nonzero_implies_two_L_full_modulus
    (N cap : ℕ) (w L : ℝ) (X P : ℕ)
    (pre : List ℕ) (p : ℕ)
    (h : upperPrimeLongBoundaryTerm
      N cap w L X P pre p ≠ 0) :
    (N : ℝ) < 2 * L * ((p :: pre).prod : ℝ) := by
  let b := (p :: pre).prod
  let a := (N - P) / b
  have hdvd : b ∣ N - P :=
    long_fibre_nonzero_full_modulus_dvd
      N cap w L X P pre p h
  have hab : a * b = N - P := by
    dsimp [a]
    exact Nat.div_mul_cancel hdvd
  have hbounds := long_fibre_nonzero_prime_window
    N cap w L X P pre p h
  have hhalf : 2 * P < N := hbounds.1
  have hpositive : 0 < N - P := by omega
  have hbpos : 0 < b := by
    by_contra hnot
    have hbzero : b = 0 := Nat.eq_zero_of_not_pos hnot
    simp [hbzero] at hab
    omega
  have haL : (a : ℝ) < L :=
    (long_fibre_nonzero_active_rosser N cap w L X P pre p h).2
  have hqcast : (a : ℝ) * (b : ℝ) =
      ((N - P : ℕ) : ℝ) := by exact_mod_cast hab
  have hqL : ((N - P : ℕ) : ℝ) < L * (b : ℝ) := by
    rw [← hqcast]
    exact mul_lt_mul_of_pos_right haL (Nat.cast_pos.mpr hbpos)
  have hNnat : N = P + (N - P) := by omega
  have hNreal : (N : ℝ) = (P : ℝ) + ((N - P : ℕ) : ℝ) := by
    exact_mod_cast hNnat
  have hhalfReal : 2 * (P : ℝ) < (N : ℝ) := by
    exact_mod_cast hhalf
  nlinarith

/-- A second, independent exact zero alternative: every LONG prime
fibre vanishes if its complete modulus times the REAL Rosser level
is at most half the target. This does not assume 2*X*z<=N. -/
theorem long_fibre_zero_of_two_L_modulus_le
    (N cap : ℕ) (w L : ℝ) (X P : ℕ)
    (pre : List ℕ) (p : ℕ)
    (hsize : 2 * L * ((p :: pre).prod : ℝ) ≤ (N : ℝ)) :
    upperPrimeLongBoundaryTerm N cap w L X P pre p = 0 := by
  by_contra hnon
  exact (not_lt_of_ge hsize)
    (long_fibre_nonzero_implies_two_L_full_modulus
      N cap w L X P pre p hnon)

/-- The original lattice restricted to actual active Rosser quotients.
This is ONLY a bounding carrier. Neither the original term nor its
original first-exit/PLUS-beta multiplier is changed. -/
def longPrimeActiveRosserWindow
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (pre : List ℕ) (p : ℕ) : Finset ℕ :=
  (longPrimeModulusWindow N X pre p).filter fun P =>
    let a := (N - P) / (p :: pre).prod
    a ∈ actualSmallRosserSupport N cap w ∧ (a : ℝ) < L

/-- Exact strict Rosser support from NONZERO, alongside the earlier
complete-modulus lattice and both original half-open endpoints. -/
theorem long_fibre_nonzero_in_active_rosser_window
    (N cap : ℕ) (w L : ℝ) (X P : ℕ)
    (pre : List ℕ) (p : ℕ)
    (h : upperPrimeLongBoundaryTerm
      N cap w L X P pre p ≠ 0) :
    P ∈ longPrimeActiveRosserWindow N cap w L X pre p := by
  exact Finset.mem_filter.mpr
    ⟨long_fibre_nonzero_in_modulus_window
      N cap w L X P pre p h,
     long_fibre_nonzero_active_rosser
      N cap w L X P pre p h⟩

/-- New invoice never exceeds the old complete-modulus lattice invoice.
The previous invoice is replaced, not summed a second time. -/
theorem active_rosser_window_card_le_modulus_card
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (pre : List ℕ) (p : ℕ) :
    (longPrimeActiveRosserWindow N cap w L X pre p).card ≤
      (longPrimeModulusWindow N X pre p).card := by
  apply Finset.card_le_card
  intro P hP
  exact (Finset.mem_filter.mp hP).1

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

/-- The ORIGINAL long prime sum is bounded by the number of actual
Rosser-active complete-modulus lattice points. Original term, beta,
fifth-power gate and strict q/half endpoints all stay unchanged. -/
theorem original_long_prime_sum_abs_le_active_rosser_card
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (pre : List ℕ) (p : ℕ) :
    |∑ P ∈ chenPrimePrefix N,
        upperPrimeLongBoundaryTerm N cap w L X P pre p| ≤
      ((longPrimeActiveRosserWindow N cap w L X pre p).card : ℝ) := by
  classical
  let W := longPrimeActiveRosserWindow N cap w L X pre p
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
        exact hpW (long_fibre_nonzero_in_active_rosser_window
          N cap w L X P pre p hn)
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
            finite_abs_sum_le_sum_abs _ _
    _ = ∑ P ∈ (chenPrimePrefix N).filter (fun P => P ∈ W),
          |upperPrimeLongBoundaryTerm N cap w L X P pre p| := hsupport
    _ ≤ ∑ P ∈ (chenPrimePrefix N).filter (fun P => P ∈ W),
          (1 : ℝ) := hterms
    _ = (((chenPrimePrefix N).filter (fun P => P ∈ W)).card : ℝ) := by
          simp
    _ ≤ (W.card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsubset

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

/-- Exactly the original signed fifth mass and ordered sixth occurrence
list. No List-to-Finset deduplication, extra mask on the source, or
duplicate payment of the earlier modulus lattice. -/
theorem original_fifth_ordered_long_prime_active_budget
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (fifth : FifthStoppedEvent ℕ) :
    |∑ P ∈ chenPrimePrefix N,
      (fifth.remainingAfter.map (fun p =>
        signedTreeCoefficient true fifth.massAfter *
          upperPrimeLongBoundaryTerm N cap w L X P
            fifth.selectedAfter p)).sum| ≤
      (fifth.remainingAfter.map (fun p =>
        |signedTreeCoefficient true fifth.massAfter| *
          ((longPrimeActiveRosserWindow
             N cap w L X fifth.selectedAfter p).card : ℝ))).sum := by
  rw [prime_list_swap fifth.remainingAfter (chenPrimePrefix N)
    (fun p P =>
      signedTreeCoefficient true fifth.massAfter *
        upperPrimeLongBoundaryTerm N cap w L X P fifth.selectedAfter p)]
  apply list_sum_abs_le_bounds
  intro p hp
  rw [← Finset.mul_sum, abs_mul]
  exact mul_le_mul_of_nonneg_left
    (original_long_prime_sum_abs_le_active_rosser_card
      N cap w L X fifth.selectedAfter p)
    (abs_nonneg _)

end
end ImbalancedChen.P4AOriginalFull87UpperPrimeActiveLevel
