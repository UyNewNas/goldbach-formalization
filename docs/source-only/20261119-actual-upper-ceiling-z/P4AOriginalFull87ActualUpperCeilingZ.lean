import ImbalancedChen.P4AOriginalFull87ActualHistoryPrunedLedger
import ImbalancedChen.P4AOriginalFull87UpperPrimeLiveZWindow
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

A SECOND genuine fifth-HISTORY zero test for the ORIGINAL upper-half
fibre: combine the literal strict 2*P<N, exact Rosser integer quotient
a=(N-P)/(p::pre).prod, a< L, and the ACTUAL sixth occurrence p<z.
A nonzero original fifth-exclusive term forces

  (N:ℝ) < 2 * (Nat.ceil L - 1) * z * fifth.selectedAfter.prod.

Thus a fifth event below this N-dependent endpoint is completely zero,
even when its older fifth-power X guard cannot remove it. Filter only
certified zero original one-sided fifthExclusive occurrences AFTER source
generation. Do not apply a mask to BOTH/sixthFromBoth, change Rosser beta,
or confuse this finite identity with an H_N payment or smooth PP input.
-/

namespace ImbalancedChen.P4AOriginalFull87ActualUpperCeilingZ
noncomputable section
open scoped Classical BigOperators

open P4AOriginalFull87FifthHistoryCeilingPrune
  (original_upper_fibre_nonzero_power_and_level
   original_fifth_ordered_upper_zero_of_history_ceiling)
open P4AOriginalFull87UpperPrimeLiveZWindow
  (actual_fifth_sixth_strictly_below_z)
open P4AOriginalFull87ActualHistoryPrunedLedger
  (keepOriginalUpperHistory)
open P4AOriginalFull87StoppedGlobalPrimeLedger
  (upperPrimeFibreTerm upperPrimeFibreEventValue
   actualStoppedUpperPrimeCoefficient
   actual_fixed_stopped_upper_primewise_strict_half)
open P4AOriginalFull87FirstFifthStoppedEvents
  (FifthStoppedEvent)
open P4AOriginalFull87FifthSixthStoppedEvents
  (FifthSixthStoppedEvent)
open P4AOriginalFull87SixthBothInvoice
  (actualFifthSixthWithoutBoth)
open P4AOriginalFull87RankFourStoppedLocalization
  (sharedRankFour)
open P4AOriginalFull87EighthPrimeMeanLedger
  (receiverTest)
open P4AOriginalFull87FifthSignedPrimitive
  (actualFixedSignedFifthTail)
open P4AOriginalFull87StoppedUpperHalfPrimeDirect
  (upperHalfReceiver)

/-- New arithmetic necessity for the ORIGINAL full upper prime fibre.
The strict N/2 boundary, integer Rosser ceiling, exact complete modulus,
and actual sixth upper endpoint are all used; no independent mask is
assumed. It is a local lemma, not an asymptotic claim. -/
theorem original_upper_fibre_nonzero_requires_ceiling_z
    (N cap : ℕ) (w L z : ℝ) (X P : ℕ)
    (pre : List ℕ) (p : ℕ)
    (hpz : (p : ℝ) < z)
    (hnon : upperPrimeFibreTerm N cap w L X P pre p ≠ 0) :
    (N : ℝ) <
      2 * (((Nat.ceil L - 1 : ℕ) : ℝ) * z * (pre.prod : ℝ)) := by
  let a : ℕ := (N - P) / (p :: pre).prod
  have hg :
      2 * P < N ∧ X < N - P ∧
      a ∈ P4AOriginalFull87PlusBetaPowerFilter.largeFifthRosserIndices
        N cap w X pre ∧
      a * (p :: pre).prod = N - P := by
    unfold upperPrimeFibreTerm at hnon
    split_ifs at hnon with hgate
    · simpa only [a] using hgate
    · contradiction
  have haL : (a : ℝ) < L :=
    (original_upper_fibre_nonzero_power_and_level
      N cap w L X P pre p hnon).2
  have hceil : a < Nat.ceil L := Nat.lt_ceil.mpr haL
  have hac : a ≤ Nat.ceil L - 1 := by omega
  have hprod : a * (p * pre.prod) = N - P := by
    simpa only [List.prod_cons] using hg.2.2.2
  have hsizeNat : N < 2 * (a * (p * pre.prod)) := by omega
  have hsizeReal :
      (N : ℝ) < 2 * ((a : ℝ) * (p : ℝ) * (pre.prod : ℝ)) := by
    have hcast : (N : ℝ) <
        ((2 * (a * (p * pre.prod)) : ℕ) : ℝ) := by
      exact_mod_cast hsizeNat
    push_cast at hcast
    nlinarith only [hcast]
  have hacReal :
      (a : ℝ) ≤ (((Nat.ceil L - 1 : ℕ) : ℝ)) := by
    exact_mod_cast hac
  have hmul :
      (a : ℝ) * (p : ℝ) ≤
      (((Nat.ceil L - 1 : ℕ) : ℝ)) * z := by
    calc
      (a : ℝ) * (p : ℝ) ≤
          (((Nat.ceil L - 1 : ℕ) : ℝ)) * (p : ℝ) :=
        mul_le_mul_of_nonneg_right hacReal (Nat.cast_nonneg _)
      _ ≤ (((Nat.ceil L - 1 : ℕ) : ℝ)) * z :=
        mul_le_mul_of_nonneg_left hpz.le (Nat.cast_nonneg _)
  have hscaled :
      2 * ((a : ℝ) * (p : ℝ) * (pre.prod : ℝ)) ≤
      2 * (((Nat.ceil L - 1 : ℕ) : ℝ) * z *
        (pre.prod : ℝ)) := by
    have hh := mul_le_mul_of_nonneg_right hmul
      (Nat.cast_nonneg pre.prod)
    nlinarith only [hh]
  exact lt_of_lt_of_le hsizeReal hscaled

/-- This is an actual-producer theorem: p<z comes from the original
receiver-generated one-sided fifth event and common rank-four parent,
not from a new free-standing source assumption. -/
theorem actual_fifth_exclusive_upper_zero_of_ceiling_z
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X P : ℕ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w z)
    (fifth : FifthStoppedEvent ℕ)
    (hfifth : FifthSixthStoppedEvent.fifthExclusive fifth ∈
      actualFifthSixthWithoutBoth delta n e q om N cap w L X
        (receiverTest N) state)
    (hcut : 2 * (((Nat.ceil L - 1 : ℕ) : ℝ) * z *
      (fifth.selectedAfter.prod : ℝ)) ≤ (N : ℝ)) :
    upperPrimeFibreEventValue N cap w L X P
      (.fifthExclusive fifth) = 0 := by
  have htermzero : ∀ p ∈ fifth.remainingAfter,
      upperPrimeFibreTerm N cap w L X P fifth.selectedAfter p = 0 := by
    intro p hp
    by_contra hnon
    have hpz := actual_fifth_sixth_strictly_below_z
      delta n e q om N cap w z L X
      state hstate fifth hfifth p hp
    exact (not_lt_of_ge hcut)
      (original_upper_fibre_nonzero_requires_ceiling_z
        N cap w L z X P fifth.selectedAfter p hpz hnon)
  have hm :
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
      simp [htermzero p hp]
    rw [hmap]
    simp
  cases hk : fifth.kind with
  | rawOnly => simpa [upperPrimeFibreEventValue, hk] using hm
  | both => simp [upperPrimeFibreEventValue, hk]
  | licensedOnly => simp [upperPrimeFibreEventValue, hk, hm]

/-- New event predicate: apply BOTH independent history-only zero
tests to original one-sided fifth events. Inherited constructors are
always kept, so no unlicensed policy mask is introduced. -/
def keepOriginalUpperHistoryWithZ (N : ℕ) (z L : ℝ) (X : ℕ) :
    FifthSixthStoppedEvent ℕ → Bool
  | .fifthExclusive fifth =>
      match fifth.kind with
      | .rawOnly =>
          decide (X ^ 5 <
            (Nat.ceil L - 1) ^ 5 * fifth.selectedAfter.prod ^ 6 ∧
            (N : ℝ) <
              2 * (((Nat.ceil L - 1 : ℕ) : ℝ) * z *
                (fifth.selectedAfter.prod : ℝ)))
      | .licensedOnly =>
          decide (X ^ 5 <
            (Nat.ceil L - 1) ^ 5 * fifth.selectedAfter.prod ^ 6 ∧
            (N : ℝ) <
              2 * (((Nat.ceil L - 1 : ℕ) : ℝ) * z *
                (fifth.selectedAfter.prod : ℝ)))
      | .both => true
  | .sixthFromBoth _ _ => true

/-- A rejected REAL producer event is exactly zero. No assumption that
all histories satisfy either guard is made: the predicate is evaluated
on each actual event, preserving all surviving occurrences. -/
theorem actual_rejected_upper_history_with_z_zero
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X P : ℕ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w z)
    (ev : FifthSixthStoppedEvent ℕ)
    (hev : ev ∈ actualFifthSixthWithoutBoth
      delta n e q om N cap w L X (receiverTest N) state)
    (hreject : keepOriginalUpperHistoryWithZ N z L X ev = false) :
    upperPrimeFibreEventValue N cap w L X P ev = 0 := by
  cases ev with
  | fifthExclusive fifth =>
      cases hk : fifth.kind with
      | rawOnly =>
          by_cases hpower : X ^ 5 <
              (Nat.ceil L - 1) ^ 5 * fifth.selectedAfter.prod ^ 6
          · by_cases hsize : (N : ℝ) <
                2 * (((Nat.ceil L - 1 : ℕ) : ℝ) * z *
                  (fifth.selectedAfter.prod : ℝ))
            · simp [keepOriginalUpperHistoryWithZ, hk,
                hpower, hsize] at hreject
            · exact actual_fifth_exclusive_upper_zero_of_ceiling_z
                delta n e q om N cap w z L X P state hstate fifth
                hev (le_of_not_gt hsize)
          · have hprev := original_fifth_ordered_upper_zero_of_history_ceiling
              N cap w L X P fifth (Nat.le_of_not_gt hpower)
            simp [upperPrimeFibreEventValue, hk, hprev]
      | both =>
          simp [keepOriginalUpperHistoryWithZ, hk] at hreject
      | licensedOnly =>
          by_cases hpower : X ^ 5 <
              (Nat.ceil L - 1) ^ 5 * fifth.selectedAfter.prod ^ 6
          · by_cases hsize : (N : ℝ) <
                2 * (((Nat.ceil L - 1 : ℕ) : ℝ) * z *
                  (fifth.selectedAfter.prod : ℝ))
            · simp [keepOriginalUpperHistoryWithZ, hk,
                hpower, hsize] at hreject
            · exact actual_fifth_exclusive_upper_zero_of_ceiling_z
                delta n e q om N cap w z L X P state hstate fifth
                hev (le_of_not_gt hsize)
          · have hprev := original_fifth_ordered_upper_zero_of_history_ceiling
              N cap w L X P fifth (Nat.le_of_not_gt hpower)
            simp [upperPrimeFibreEventValue, hk, hprev]
  | sixthFromBoth _ _ =>
      simp [keepOriginalUpperHistoryWithZ] at hreject

private theorem ordered_sum_delete_certified_zeros
    {α : Type*} (xs : List α) (keep : α → Bool) (f : α → ℝ)
    (hz : ∀ x ∈ xs, keep x = false → f x = 0) :
    (xs.map f).sum = ((xs.filter keep).map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx := hz x (by simp)
      have htail : ∀ y ∈ xs, keep y = false → f y = 0 := by
        intro y hy hk
        exact hz y (by simp [hy]) hk
      cases hk : keep x with
      | false =>
          have hv : f x = 0 := hx hk
          simpa [List.filter, hk, hv] using ih htail
      | true =>
          simpa [List.filter, hk] using
            congrArg (fun t : ℝ => f x + t) (ih htail)

/-- An exact, source-generated, unconditionally valid global upper
coefficient after a STRICTER proven-zero deletion. The original policy,
receiver, fifth mass and ordered sixth occurrences are unchanged. -/
def actualUpperCeilingZLiveCoefficient
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X P : ℕ) : ℝ :=
  ((sharedRankFour e q om N cap w z).map (fun state =>
    (((actualFifthSixthWithoutBoth delta n e q om N cap w L X
        (receiverTest N) state).filter
          (keepOriginalUpperHistoryWithZ N z L X)).map
      (upperPrimeFibreEventValue N cap w L X P)).sum)).sum

theorem original_actual_upper_coefficient_eq_ceiling_z_live
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X P : ℕ) :
    actualStoppedUpperPrimeCoefficient delta n e q om N cap w z L X P =
      actualUpperCeilingZLiveCoefficient delta n e q om
        N cap w z L X P := by
  unfold actualStoppedUpperPrimeCoefficient
    actualUpperCeilingZLiveCoefficient
  apply congrArg List.sum
  apply List.map_congr_left
  intro state hstate
  exact ordered_sum_delete_certified_zeros
    (actualFifthSixthWithoutBoth delta n e q om N cap w L X
      (receiverTest N) state)
    (keepOriginalUpperHistoryWithZ N z L X)
    (upperPrimeFibreEventValue N cap w L X P)
    (fun ev hev hr =>
      actual_rejected_upper_history_with_z_zero
        delta n e q om N cap w z L X P
        state hstate ev hev hr)

theorem actual_stopped_upper_eq_ceiling_z_live_primewise
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) :
    actualFixedSignedFifthTail delta n e q om N cap w z L X
      (upperHalfReceiver N) =
    ∑ P ∈ (chenPrimePrefix N).filter (fun P => 2 * P < N),
      actualUpperCeilingZLiveCoefficient delta n e q om
        N cap w z L X P := by
  rw [actual_fixed_stopped_upper_primewise_strict_half]
  apply Finset.sum_congr rfl
  intro P _
  exact original_actual_upper_coefficient_eq_ceiling_z_live
    delta n e q om N cap w z L X P

end
end ImbalancedChen.P4AOriginalFull87ActualUpperCeilingZ
