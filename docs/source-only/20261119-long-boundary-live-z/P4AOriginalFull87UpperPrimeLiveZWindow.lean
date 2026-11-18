import ImbalancedChen.P4AOriginalFull87UpperPrimeShortBoundary
import ImbalancedChen.P4AOriginalFull87OrderedSixthSuffix
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

The original fifthExclusive receiver event and the ORIGINAL sorted rough
universe imply that each real sixth occurrence p obeys (p : ℝ) < z.
An unpaid upper-half LONG product term is then confined simultaneously to

    N - X*p ≤ P,    2*P < N,    X < N-P,    p < z,    N < 2*X*p,

and therefore N < 2*(X : ℝ)*z.  This is not a numerical producer-X
bound: X remains the literal natural parameter supplied by the actual
producer.  The long boundary vanishes when 2*X*z ≤ N, including ALL
ordered sixth occurrences of that actual fifth event, preserving its
genuine signed mass and the one-time short/long decomposition.

No new axioms, input distributions, smooth PP, or physical reweighting.
-/

namespace ImbalancedChen.P4AOriginalFull87UpperPrimeLiveZWindow
noncomputable section
open scoped Classical BigOperators

open P4AOriginalFull87RankFourStoppedLocalization (sharedRankFour)
open P4AOriginalFull87SixthBothInvoice (actualFifthSixthWithoutBoth)
open P4AOriginalFull87FirstFifthStoppedEvents (FifthStoppedEvent)
open P4AOriginalFull87FifthSixthStoppedEvents (FifthSixthStoppedEvent)
open P4AOriginalFull87OrderedSixthSuffix
  (actual_event_joined_history_original_rough)
open P4AOriginalFull87EighthPrimeMeanLedger (receiverTest)
open P4AOriginalFull87StoppedGlobalPrimeLedger (upperPrimeFibreTerm)
open P4AOriginalFull87UpperPrimeShortBoundary
  (upperPrimeShortNoPowerTerm upperPrimeLongBoundaryTerm
   actual_fifth_prime_boundary_invoice
   long_boundary_nonzero_implies_large_Xp)

/-- Derive the literal strict upper cutoff for a SIXTH occurrence from
its actual full selected-history-plus-tail Sublist, without attaching an
independent prime mask or changing the descending source List. -/
theorem actual_fifth_sixth_strictly_below_z
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w z)
    (fifth : FifthStoppedEvent ℕ)
    (hfifth : FifthSixthStoppedEvent.fifthExclusive fifth ∈
      actualFifthSixthWithoutBoth delta n e q om N cap w L X
        (receiverTest N) state)
    (p : ℕ) (hp : p ∈ fifth.remainingAfter) :
    (p : ℝ) < z := by
  have hjoined :
      fifth.selectedAfter.reverse ++ fifth.remainingAfter <+
        roughPrimeUniverse N cap w z := by
    simpa [P4AOriginalFull87OrderedSixthSuffix.eventSelected,
      P4AOriginalFull87ActualSixthSuffix.eventSixthSuffix] using
      (actual_event_joined_history_original_rough
        delta n e q om N cap w z L X (receiverTest N)
        state hstate (.fifthExclusive fifth) hfifth)
  have hmem : p ∈ roughPrimeUniverse N cap w z :=
    hjoined.subset (List.mem_append.mpr (Or.inr hp))
  exact mem_roughPrimeUniverse_upper hmem

/-- The UNMODIFIED long fibre has a genuine narrow original-prime
window. Endpoints are kept with their original strictness; P is only
declared prime by an enclosing chenPrimePrefix sum, not by this lemma. -/
theorem long_fibre_nonzero_prime_window
    (N cap : ℕ) (w L : ℝ) (X P : ℕ)
    (pre : List ℕ) (p : ℕ)
    (h : upperPrimeLongBoundaryTerm N cap w L X P pre p ≠ 0) :
    2 * P < N ∧ N - X * p ≤ P ∧ X < N - P ∧
      N < 2 * (X * p) := by
  have hnshort : ¬ X * p < N - P := by
    intro hs
    have hz : upperPrimeLongBoundaryTerm N cap w L X P pre p = 0 := by
      simp [upperPrimeLongBoundaryTerm, hs]
    exact h hz
  have hhalf : 2 * P < N := by
    by_contra hn
    have hz : upperPrimeLongBoundaryTerm N cap w L X P pre p = 0 := by
      simp [upperPrimeLongBoundaryTerm, upperPrimeFibreTerm, hnshort, hn]
    exact h hz
  have hhigh : X < N - P := by
    by_contra hn
    have hz : upperPrimeLongBoundaryTerm N cap w L X P pre p = 0 := by
      simp [upperPrimeLongBoundaryTerm, upperPrimeFibreTerm, hnshort, hn]
    exact h hz
  have hq : N - P ≤ X * p := Nat.le_of_not_gt hnshort
  have hwindow : N - X * p ≤ P := by omega
  exact ⟨hhalf, hwindow, hhigh,
    long_boundary_nonzero_implies_large_Xp N cap w L X P pre p h⟩

/-- A nonzero term from a GENUINE actual fifth/sixth occurrence forces
the global endpoint violation N < 2*X*z. The rough upper endpoint z,
NOT the lower endpoint w, is the only real cutoff used here. -/
theorem actual_long_boundary_nonzero_implies_two_X_z
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X P : ℕ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w z)
    (fifth : FifthStoppedEvent ℕ)
    (hfifth : FifthSixthStoppedEvent.fifthExclusive fifth ∈
      actualFifthSixthWithoutBoth delta n e q om N cap w L X
        (receiverTest N) state)
    (p : ℕ) (hp : p ∈ fifth.remainingAfter)
    (hnon : upperPrimeLongBoundaryTerm
      N cap w L X P fifth.selectedAfter p ≠ 0) :
    (N : ℝ) < 2 * (X : ℝ) * z := by
  have hsize : N < 2 * (X * p) :=
    (long_fibre_nonzero_prime_window
      N cap w L X P fifth.selectedAfter p hnon).2.2.2
  have hXnat : 0 < X := by
    by_contra hn
    have hx0 : X = 0 := Nat.eq_zero_of_not_pos hn
    simp [hx0] at hsize
  have hXpos : 0 < (2 : ℝ) * (X : ℝ) :=
    mul_pos (by norm_num) (Nat.cast_pos.mpr hXnat)
  have hpz : (p : ℝ) < z :=
    actual_fifth_sixth_strictly_below_z
      delta n e q om N cap w z L X state hstate fifth hfifth p hp
  have hcast : (N : ℝ) < (2 * (X * p) : ℕ) := by
    exact_mod_cast hsize
  calc
    (N : ℝ) < 2 * (X : ℝ) * (p : ℝ) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using hcast
    _ < 2 * (X : ℝ) * z :=
      mul_lt_mul_of_pos_left hpz hXpos

/-- A single *real-upper-cutoff* condition eliminates the exact unpaid
long prime term at each actual sixth occurrence. This discharges the
earlier per-occurrence bound, but does NOT establish that the actual
producer parameters satisfy the condition. -/
theorem actual_long_boundary_zero_of_two_X_z_le
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X P : ℕ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w z)
    (fifth : FifthStoppedEvent ℕ)
    (hfifth : FifthSixthStoppedEvent.fifthExclusive fifth ∈
      actualFifthSixthWithoutBoth delta n e q om N cap w L X
        (receiverTest N) state)
    (p : ℕ) (hp : p ∈ fifth.remainingAfter)
    (hcut : 2 * (X : ℝ) * z ≤ (N : ℝ)) :
    upperPrimeLongBoundaryTerm N cap w L X P fifth.selectedAfter p = 0 := by
  by_contra hn
  have hviolation := actual_long_boundary_nonzero_implies_two_X_z
    delta n e q om N cap w z L X P
    state hstate fifth hfifth p hp hn
  exact (not_lt_of_ge hcut) hviolation

/-- Pay the long boundary exactly ZERO, when justified by the physical
upper endpoint, over the genuine ORDERED sixth list and its original
fifth signed mass. No Finset-based deduplication or double invoice. -/
theorem actual_fifth_long_boundary_zero_of_two_X_z_le
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X P : ℕ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w z)
    (fifth : FifthStoppedEvent ℕ)
    (hfifth : FifthSixthStoppedEvent.fifthExclusive fifth ∈
      actualFifthSixthWithoutBoth delta n e q om N cap w L X
        (receiverTest N) state)
    (hcut : 2 * (X : ℝ) * z ≤ (N : ℝ)) :
    (fifth.remainingAfter.map (fun p =>
      signedTreeCoefficient true fifth.massAfter *
        upperPrimeLongBoundaryTerm N cap w L X P fifth.selectedAfter p)).sum =
      0 := by
  have hmap :
      fifth.remainingAfter.map (fun p =>
        signedTreeCoefficient true fifth.massAfter *
          upperPrimeLongBoundaryTerm N cap w L X P fifth.selectedAfter p) =
      fifth.remainingAfter.map (fun _ => (0 : ℝ)) := by
    apply List.map_congr_left
    intro p hp
    simp [actual_long_boundary_zero_of_two_X_z_le
      delta n e q om N cap w z L X P
      state hstate fifth hfifth p hp hcut]
  rw [hmap]
  simp

/-- The one-time original short/long invoice now has no long term
whenever the REAL rough upper endpoint and actual X satisfy 2*X*z<=N.
The small-Rosser arithmetic quotient in the short term stays intact. -/
theorem actual_fifth_prime_short_only_of_two_X_z_le
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X P : ℕ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w z)
    (fifth : FifthStoppedEvent ℕ)
    (hfifth : FifthSixthStoppedEvent.fifthExclusive fifth ∈
      actualFifthSixthWithoutBoth delta n e q om N cap w L X
        (receiverTest N) state)
    (hcut : 2 * (X : ℝ) * z ≤ (N : ℝ)) :
    (fifth.remainingAfter.map (fun p =>
      signedTreeCoefficient true fifth.massAfter *
        upperPrimeFibreTerm N cap w L X P fifth.selectedAfter p)).sum =
      (fifth.remainingAfter.map (fun p =>
        signedTreeCoefficient true fifth.massAfter *
          upperPrimeShortNoPowerTerm N cap w L X P fifth.selectedAfter p)).sum := by
  rw [actual_fifth_prime_boundary_invoice
    delta n e q om N cap w z L X P state hstate fifth hfifth,
    actual_fifth_long_boundary_zero_of_two_X_z_le
      delta n e q om N cap w z L X P state hstate fifth hfifth hcut]
  simp

end
end ImbalancedChen.P4AOriginalFull87UpperPrimeLiveZWindow
