import ImbalancedChen.P4AOriginalFull87UpperActiveQuotientGap
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

A new fifth-HISTORY-only arithmetic deletion test on the ORIGINAL full
upper-half stopped prime fibre (not just its LONG boundary).
The retained fifth-power Rosser gate is
  X^5 < a^5 * selectedAfter.prod^6
and nonzero actual PLUS beta forces a < L. Since a is INTEGRAL,
  a <= Nat.ceil L - 1.
Thus no prime, no sixth occurrence, and no original signed term can
survive when
  (Nat.ceil L - 1)^5 * selectedAfter.prod^6 <= X^5.
This test depends only on the actual fifth history, not on p or P.
It is conditional; it is not asserted for all genuine producer events.
No new PP input, altered coefficient, arithmetic mask, or reserve.
-/

namespace ImbalancedChen.P4AOriginalFull87FifthHistoryCeilingPrune
noncomputable section
open scoped Classical BigOperators

open P4AOriginalFull87StoppedGlobalPrimeLedger (upperPrimeFibreTerm)
open P4AOriginalFull87UpperPrimeShortBoundary (upperPrimeLongBoundaryTerm)
open P4AOriginalFull87FirstFifthStoppedEvents (FifthStoppedEvent)
open P4AOriginalFull87PlusBetaPowerFilter (largeFifthRosserIndices)

/-- Nonzero of the literal prime fibre simultaneously requires its
original fifth POWER gate and nonzero actual beta PLUS. In particular,
the upper Rosser level belongs to the very same quotient a. -/
theorem original_upper_fibre_nonzero_power_and_level
    (N cap : ℕ) (w L : ℝ) (X P : ℕ)
    (pre : List ℕ) (p : ℕ)
    (h : upperPrimeFibreTerm N cap w L X P pre p ≠ 0) :
    let a := (N - P) / (p :: pre).prod
    X ^ 5 < a ^ 5 * pre.prod ^ 6 ∧ (a : ℝ) < L := by
  unfold upperPrimeFibreTerm at h
  split_ifs at h with hg
  · rcases hg with ⟨_, _, hRosser, _⟩
    exact ⟨(Finset.mem_filter.mp hRosser).2,
      (actualSmallRosserPlus_active h).2.1⟩
  · contradiction

/-- Integral ceiling sharpened fifth-history requirement for EVERY
nonzero ORIGINAL upper fibre, not merely the LONG invoice.
No positivity of L or pre.prod is independently assumed. -/
theorem original_upper_fibre_nonzero_requires_history_room
    (N cap : ℕ) (w L : ℝ) (X P : ℕ)
    (pre : List ℕ) (p : ℕ)
    (h : upperPrimeFibreTerm N cap w L X P pre p ≠ 0) :
    X ^ 5 < (Nat.ceil L - 1) ^ 5 * pre.prod ^ 6 := by
  let a := (N - P) / (p :: pre).prod
  obtain ⟨hpow, haL⟩ :=
    original_upper_fibre_nonzero_power_and_level
      N cap w L X P pre p h
  have hceil : a < Nat.ceil L := Nat.lt_ceil.mpr haL
  have habound : a ≤ Nat.ceil L - 1 := by omega
  have hpowle : a ^ 5 ≤ (Nat.ceil L - 1) ^ 5 := by
    gcongr <;> omega
  have hprodle :
      a ^ 5 * pre.prod ^ 6 ≤
        (Nat.ceil L - 1) ^ 5 * pre.prod ^ 6 :=
    Nat.mul_le_mul_right _ hpowle
  exact lt_of_lt_of_le hpow hprodle

/-- If the largest permitted INTEGRAL Rosser index is too small
to pass the ORIGINAL fifth-power filter, the ENTIRE prime fibre
is zero, independently of its sixth prime and of the prime P. -/
theorem original_upper_fibre_zero_of_history_ceiling
    (N cap : ℕ) (w L : ℝ) (X P : ℕ)
    (pre : List ℕ) (p : ℕ)
    (hno : (Nat.ceil L - 1) ^ 5 * pre.prod ^ 6 ≤ X ^ 5) :
    upperPrimeFibreTerm N cap w L X P pre p = 0 := by
  by_contra hnon
  have hroom :=
    original_upper_fibre_nonzero_requires_history_room
      N cap w L X P pre p hnon
  omega

/-- The old LONG boundary also vanishes under the history-only
condition; this is not a second deletion or a second invoice. -/
theorem original_long_fibre_zero_of_history_ceiling
    (N cap : ℕ) (w L : ℝ) (X P : ℕ)
    (pre : List ℕ) (p : ℕ)
    (hno : (Nat.ceil L - 1) ^ 5 * pre.prod ^ 6 ≤ X ^ 5) :
    upperPrimeLongBoundaryTerm N cap w L X P pre p = 0 := by
  simp [upperPrimeLongBoundaryTerm,
    original_upper_fibre_zero_of_history_ceiling
      N cap w L X P pre p hno]

/-- Exact cancellation of the ORIGINAL fifth stopped signed occurrence
list. All sixth positions (including repeated ones) remain in the
same ordered List; the original signed fifth mass is untouched.
The condition needs the fifth history ONLY, not per-sixth assumptions. -/
theorem original_fifth_ordered_upper_zero_of_history_ceiling
    (N cap : ℕ) (w L : ℝ) (X P : ℕ)
    (fifth : FifthStoppedEvent ℕ)
    (hno : (Nat.ceil L - 1) ^ 5 *
      fifth.selectedAfter.prod ^ 6 ≤ X ^ 5) :
    (fifth.remainingAfter.map (fun p =>
      signedTreeCoefficient true fifth.massAfter *
        upperPrimeFibreTerm N cap w L X P
          fifth.selectedAfter p)).sum = 0 := by
  have hmap :
      fifth.remainingAfter.map (fun p =>
        signedTreeCoefficient true fifth.massAfter *
          upperPrimeFibreTerm N cap w L X P
            fifth.selectedAfter p) =
      fifth.remainingAfter.map (fun _ => (0 : ℝ)) := by
    apply List.map_congr_left
    intro p hp
    simp [original_upper_fibre_zero_of_history_ceiling
      N cap w L X P fifth.selectedAfter p hno]
  rw [hmap]
  simp

/-- The same one-time deletion after summing the original prime
prefix. This theorem does not replace the prefix by a smooth PP input
and does not infer a signed saving from cap monotonicity. -/
theorem original_fifth_upper_prime_sum_zero_of_history_ceiling
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (fifth : FifthStoppedEvent ℕ)
    (hno : (Nat.ceil L - 1) ^ 5 *
      fifth.selectedAfter.prod ^ 6 ≤ X ^ 5) :
    (∑ P ∈ chenPrimePrefix N,
      (fifth.remainingAfter.map (fun p =>
        signedTreeCoefficient true fifth.massAfter *
          upperPrimeFibreTerm N cap w L X P
            fifth.selectedAfter p)).sum) = 0 := by
  apply Finset.sum_eq_zero
  intro P hP
  exact original_fifth_ordered_upper_zero_of_history_ceiling
    N cap w L X P fifth hno

end
end ImbalancedChen.P4AOriginalFull87FifthHistoryCeilingPrune
