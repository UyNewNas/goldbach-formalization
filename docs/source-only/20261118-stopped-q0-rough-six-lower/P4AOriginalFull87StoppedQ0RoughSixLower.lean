import ImbalancedChen.P4AOriginalFull87StoppedCentreExceptionFibre
import ImbalancedChen.P4AOriginalFull87FifthRankPowerTail
import ImbalancedChen.P4AOriginalFull87OrderedSixthSuffix
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

An independent, quantitative support obstruction for the ORIGINAL stopped
q0=(N-2)/2 centre correction. Six ACTUAL rough-prime factors, including
the actual sixth candidate and all five selected-history factors, are
each at least the LITERAL lower rough cutoff w. Consequently a positive
original full modulus a*b6=q0 forces (q0:Real) >= w^6.

This requires only the existing ordered joined-history sublist and the
original real half-open rough-prime universe; no new event source,
sieve coefficients, mask or assumed power-law identification for w.
The consequent full stopped cancellation is conditional on the ACTUAL
numeric inequality (q0:Real) < w^6; the manuscript specialization of
w must be proved separately before any unconditional asymptotic claim.
-/

namespace ImbalancedChen.P4AOriginalFull87StoppedQ0RoughSixLower
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87StoppedCentreExceptionFibre
  (exceptionalCentreFibre exceptionalFifthPlusFibre
   common_sixth_exceptional_fibre_eq_original_weights
   actual_fixed_fifth_centre_eq_lower_plus_exception)
open P4AOriginalFull87FirstFifthStoppedEvents (FifthStoppedEvent)
open P4AOriginalFull87FifthSixthStoppedEvents (FifthSixthStoppedEvent)
open P4AOriginalFull87SixthBothInvoice (actualFifthSixthWithoutBoth)
open P4AOriginalFull87RankFourStoppedLocalization (sharedRankFour)
open P4AOriginalFull87CommonSixthSignedKernel
  (commonLargeSixthKernel commonSignedEventValue)
open P4AOriginalFull87FifthSignedPrimitive
  (actualFixedSignedFifthTail)
open P4AOriginalFull87FifthRankPowerTail
  (actual_fifth_exclusive_length_five)
open P4AOriginalFull87OrderedSixthSuffix
  (actual_event_joined_history_original_rough)
open P4AOriginalFull87EighthPrimeMeanLedger (receiverTest)
open P4AOriginalFull87StoppedCentreUpperThird (lowerThirdCentre)

/-- Literal product of a list of natural numbers dominates the power
of any nonnegative real lower bound on every listed occurrence.
No conversion of the occurrence list into a set. -/
private theorem rough_cutoff_pow_length_le_product
    (xs : List ℕ) (w : ℝ) (hw : 0 ≤ w)
    (hlo : ∀ r ∈ xs, w ≤ (r : ℝ)) :
    w ^ xs.length ≤ (xs.prod : ℝ) := by
  induction xs generalizing hlo with
  | nil =>
      simp
  | cons r rs ih =>
      have hr : w ≤ (r : ℝ) := hlo r (by simp)
      have hrest : ∀ t ∈ rs, w ≤ (t : ℝ) := by
        intro t ht
        exact hlo t (by simp [ht])
      have htail := ih hrest
      calc
        w ^ (r :: rs).length = w * w ^ rs.length := by
          simp only [List.length_cons]
          rw [pow_succ]
          ring
        _ ≤ (r : ℝ) * (rs.prod : ℝ) :=
          mul_le_mul hr htail (pow_nonneg hw _) (Nat.cast_nonneg _)
        _ = ((r :: rs).prod : ℝ) := by simp [List.prod_cons]

/-- The six ORIGINAL rough factors force the literal full modulus
to be at least w^6 (over reals). The Rosser index a is not dropped:
a >= 1 follows from the positive actual q0 and the exact equality. -/
private theorem six_rough_factors_force_full_modulus_lower
    (N a : ℕ) (w : ℝ) (p : ℕ) (pre : List ℕ)
    (hN : 8 ≤ N) (hw : 0 ≤ w)
    (hlen : pre.length = 5)
    (hlo : ∀ r ∈ p :: pre, w ≤ (r : ℝ))
    (heq : a * (p :: pre).prod = (N - 2) / 2) :
    w ^ 6 ≤ (((N - 2) / 2 : ℕ) : ℝ) := by
  have hpos : 0 < (N - 2) / 2 := by omega
  have ha : 0 < a := by
    by_contra h
    have ha0 : a = 0 := Nat.eq_zero_of_not_pos h
    have hzero : (N - 2) / 2 = 0 := by
      simpa [ha0] using heq.symm
    omega
  have ha1N : 1 ≤ a := by omega
  have ha1 : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha1N
  have hword := rough_cutoff_pow_length_le_product
    (p :: pre) w hw hlo
  have hwordlen : (p :: pre).length = 6 := by simp [hlen]
  rw [hwordlen] at hword
  have hmul : ((p :: pre).prod : ℝ) ≤
      (((N - 2) / 2 : ℕ) : ℝ) := by
    have hcast : (a : ℝ) * ((p :: pre).prod : ℝ) =
        (((N - 2) / 2 : ℕ) : ℝ) := by
      exact_mod_cast heq
    calc
      ((p :: pre).prod : ℝ) =
          (1 : ℝ) * ((p :: pre).prod : ℝ) := by ring
      _ ≤ (a : ℝ) * ((p :: pre).prod : ℝ) :=
        mul_le_mul_of_nonneg_right ha1 (Nat.cast_nonneg _)
      _ = (((N - 2) / 2 : ℕ) : ℝ) := hcast
  exact le_trans hword hmul

/-- For a REAL receiver-generated fifth-exclusive event, the original
PLUS-beta q0 fibre is exactly zero whenever the existing rough lower
cutoff already makes six physical rough primes too large. In particular
this does not assume q0 has fewer than six prime divisors. -/
theorem actual_fifth_q0_plus_zero_of_rough_six_cutoff
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w z)
    (fifth : FifthStoppedEvent ℕ)
    (hfifth : FifthSixthStoppedEvent.fifthExclusive fifth ∈
      actualFifthSixthWithoutBoth delta n e q om N cap w L X
        (receiverTest N) state)
    (p : ℕ) (hp : p ∈ fifth.remainingAfter)
    (hN : 8 ≤ N) (hw : 0 ≤ w)
    (hcut : (((N - 2) / 2 : ℕ) : ℝ) < w ^ 6) :
    exceptionalFifthPlusFibre N cap w L X fifth.selectedAfter p = 0 := by
  have hlen : fifth.selectedAfter.length = 5 :=
    actual_fifth_exclusive_length_five
      delta n e q om N cap w z L X (receiverTest N)
      state hstate fifth hfifth
  have hjoin :
      fifth.selectedAfter.reverse ++ fifth.remainingAfter <+
        roughPrimeUniverse N cap w z := by
    simpa [P4AOriginalFull87OrderedSixthSuffix.eventSelected,
      P4AOriginalFull87ActualSixthSuffix.eventSixthSuffix] using
      (actual_event_joined_history_original_rough
        delta n e q om N cap w z L X (receiverTest N)
        state hstate (.fifthExclusive fifth) hfifth)
  have hlo (r : ℕ) (hr : r ∈ p :: fifth.selectedAfter) :
      w ≤ (r : ℝ) := by
    rcases List.mem_cons.mp hr with h | hpre
    · subst r
      exact mem_roughPrimeUniverse_lower
        (hjoin.subset (List.mem_append.mpr (Or.inr hp)))
    · have hrrev : r ∈ fifth.selectedAfter.reverse := by
        simpa using hpre
      exact mem_roughPrimeUniverse_lower
        (hjoin.subset (List.mem_append.mpr (Or.inl hrrev)))
  unfold exceptionalFifthPlusFibre
  apply Finset.sum_eq_zero
  intro a ha
  have hneq :
      a * (p :: fifth.selectedAfter).prod ≠ (N - 2) / 2 := by
    intro heq
    have hbound := six_rough_factors_force_full_modulus_lower
      N a w p fifth.selectedAfter hN hw hlen hlo heq
    exact (not_lt_of_ge hbound) hcut
  simp [hneq]

/-- Original occurrence-sensitive stopped signed q0 coefficient is zero
under the SAME literal physical cutoff. Fifth-event masses, PLUS-beta,
sixth occurrence multiplicity and real sharedRankFour are unchanged. -/
theorem actual_fixed_fifth_q0_zero_of_rough_six_cutoff
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ)
    (hN : 8 ≤ N) (hw : 0 ≤ w)
    (hcut : (((N - 2) / 2 : ℕ) : ℝ) < w ^ 6) :
    actualFixedSignedFifthTail delta n e q om N cap w z L X
      (exceptionalCentreFibre N) = 0 := by
  let events : FirstExitDepthState ℕ →
      List (FifthSixthStoppedEvent ℕ) :=
    fun state => actualFifthSixthWithoutBoth
      delta n e q om N cap w L X (receiverTest N) state
  have hevent (state : FirstExitDepthState ℕ)
      (hs : state ∈ sharedRankFour e q om N cap w z)
      (ev : FifthSixthStoppedEvent ℕ) (hev : ev ∈ events state) :
      commonSignedEventValue N cap w L X (exceptionalCentreFibre N) ev = 0 := by
    cases ev with
    | fifthExclusive fifth =>
        have hkernel : commonLargeSixthKernel N cap w L X
            (exceptionalCentreFibre N) fifth = 0 := by
          rw [common_sixth_exceptional_fibre_eq_original_weights]
          have hmap :
              (fifth.remainingAfter.map (fun p =>
                signedTreeCoefficient true fifth.massAfter *
                  exceptionalFifthPlusFibre N cap w L X
                    fifth.selectedAfter p)) =
              fifth.remainingAfter.map (fun _ => (0 : ℝ)) := by
            apply List.map_congr_left
            intro p hp
            rw [actual_fifth_q0_plus_zero_of_rough_six_cutoff
              delta n e q om N cap w z L X state hs fifth hev p hp
              hN hw hcut]
            simp
          rw [hmap]
          simp
        cases hk : fifth.kind <;>
          simp [commonSignedEventValue, hk, hkernel]
    | sixthFromBoth pre fifth =>
        simp [commonSignedEventValue]
  change ((sharedRankFour e q om N cap w z).map (fun state =>
    (((events state).map
      (commonSignedEventValue N cap w L X
        (exceptionalCentreFibre N))).sum))).sum = 0
  have houter :
      (sharedRankFour e q om N cap w z).map (fun state =>
        (((events state).map
          (commonSignedEventValue N cap w L X
            (exceptionalCentreFibre N))).sum)) =
      (sharedRankFour e q om N cap w z).map (fun _ => (0 : ℝ)) := by
    apply List.map_congr_left
    intro state hs
    have hinner :
        (events state).map (commonSignedEventValue N cap w L X
          (exceptionalCentreFibre N)) =
        (events state).map (fun _ => (0 : ℝ)) := by
      apply List.map_congr_left
      intro ev hev
      exact hevent state hs ev hev
    rw [hinner]
    simp
  rw [houter]
  simp

/-- Exact centre invoice transfer for the true stopped list, only
on an explicit physical-rough-cutoff subfamily. No extra centre payment. -/
theorem actual_fixed_fifth_centre_eq_lower_of_rough_six_cutoff
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ)
    (hcomp : ¬ Nat.Prime N) (hmod : N % 4 = 0)
    (hN : 8 ≤ N) (hw : 0 ≤ w)
    (hcut : (((N - 2) / 2 : ℕ) : ℝ) < w ^ 6) :
    actualFixedSignedFifthTail delta n e q om N cap w z L X
      (chenCentrePrimeAPCount N N) =
    actualFixedSignedFifthTail delta n e q om N cap w z L X
      (lowerThirdCentre N) := by
  rw [actual_fixed_fifth_centre_eq_lower_plus_exception
    delta n e q om N cap w z L X hcomp hmod hN]
  rw [actual_fixed_fifth_q0_zero_of_rough_six_cutoff
    delta n e q om N cap w z L X hN hw hcut]
  ring

end
end ImbalancedChen.P4AOriginalFull87StoppedQ0RoughSixLower
