import ImbalancedChen.P4AOriginalFull87Rho0SixCutoff
import ImbalancedChen.P4AOriginalFull87FifthSignedPrimitive
import ImbalancedChen.P4AOriginalFull87OrderedSixthSuffix
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

A stronger consequence of the preceding six-rough-prime arithmetic:
at the literal upper cutoff w=N^(19/96), the original actual receiver
source has NO positive sixth continuation at any complete PLUS-beta
modulus, not merely at the isolated centre-prime q0 fibre.

This proof uses the SAME actual receiverTest N in the real event
producer; it does NOT replace the event source by a separate AP model.
The complete a*(p::selected).prod modulus and the original ordered
sixth occurrence list are kept. This does NOT identify any upstream
generic-w caller with the manuscript upper cutoff.
-/

namespace ImbalancedChen.P4AOriginalFull87UpperRho0SixReceiver
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87Rho0SixCutoff (upper_rho0_six_power_gt_N)
open P4AOriginalFull87EighthPrimeMeanLedger (receiverTest)
open P4AOriginalFull87FifthSignedPrimitive (actualFixedSignedFifthTail)
open P4AOriginalFull87OrderedSixthSuffix
  (actual_event_joined_history_original_rough)
open P4AOriginalFull87FifthRankPowerTail
  (actual_fifth_exclusive_length_five)
open P4AOriginalFull87FirstFifthStoppedEvents (FifthStoppedEvent)
open P4AOriginalFull87FifthSixthStoppedEvents (FifthSixthStoppedEvent)
open P4AOriginalFull87SixthBothInvoice (actualFifthSixthWithoutBoth)
open P4AOriginalFull87RankFourStoppedLocalization (sharedRankFour)
open P4AOriginalFull87CommonSixthSignedKernel
  (commonLargeSixthKernel commonSignedEventValue
   actual_stopped_difference_eq_common_signed_sixth_kernel)
open P4AOriginalFull87PlusBetaPowerFilter
  (largeFifthPlusAttachment largeFifthRosserIndices)
open P4AOriginalFull87EarlyStopPhysicalGap (rawStopped licensedStopped)

/-- An exact receiver is a positive integer at most N. A larger complete
modulus divides no receiver at all. The d=0 case is also covered. -/
theorem receiverTest_zero_of_modulus_gt_N (N d : ℕ) (hd : N < d) :
    receiverTest N d = 0 := by
  unfold receiverTest
  have hnil :
      (chenPrimeReceiverSource N).filter (fun x => d ∣ x) = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro x hx
    obtain ⟨hsrc, hdiv⟩ := Finset.mem_filter.mp hx
    obtain ⟨hxpos, hxle, _⟩ := chenPrimeReceiverSource_data hsrc
    have hdle : d ≤ x := Nat.le_of_dvd hxpos hdiv
    omega
  simp [hnil]

/-- Six actual rough factors still dominate w^6 even on a List with
occurrences. This bound is for the FULL receiver modulus, not only q0. -/
private theorem rough_word_pow_le_prod
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

/-- A positive original Rosser index cannot reduce a six-rough-prime
modulus below the target N once w^6>N. -/
private theorem six_rough_full_modulus_gt_N
    (N a p : ℕ) (pre : List ℕ) (w : ℝ)
    (hw : 0 ≤ w) (hlen : pre.length = 5)
    (hlo : ∀ r ∈ p :: pre, w ≤ (r : ℝ))
    (ha : 0 < a) (hcut : (N : ℝ) < w ^ 6) :
    N < a * (p :: pre).prod := by
  have hword := rough_word_pow_le_prod (p :: pre) w hw hlo
  have hwordlen : (p :: pre).length = 6 := by simp [hlen]
  rw [hwordlen] at hword
  have ha1 : (1 : ℝ) ≤ (a : ℝ) := by
    exact_mod_cast (show 1 ≤ a by omega)
  have hmul : ((p :: pre).prod : ℝ) ≤
      ((a * (p :: pre).prod : ℕ) : ℝ) := by
    calc
      ((p :: pre).prod : ℝ) =
          (1 : ℝ) * ((p :: pre).prod : ℝ) := by ring
      _ ≤ (a : ℝ) * ((p :: pre).prod : ℝ) :=
        mul_le_mul_of_nonneg_right ha1 (Nat.cast_nonneg _)
      _ = ((a * (p :: pre).prod : ℕ) : ℝ) := by norm_cast
  have hreal : (N : ℝ) <
      ((a * (p :: pre).prod : ℕ) : ℝ) :=
    lt_of_lt_of_le hcut (le_trans hword hmul)
  exact_mod_cast hreal

/-- Every original PLUS-beta full modulus in an actual fifth-exclusive
receiver event is greater than N, if N<w^6. Thus its receiver count
vanishes TERM BY TERM, without taking an unsigned bound on a signed sum. -/
theorem actual_fifth_receiver_plus_zero_of_six_cutoff
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w z)
    (fifth : FifthStoppedEvent ℕ)
    (hfifth : FifthSixthStoppedEvent.fifthExclusive fifth ∈
      actualFifthSixthWithoutBoth delta n e q om N cap w L X
        (receiverTest N) state)
    (p : ℕ) (hp : p ∈ fifth.remainingAfter)
    (hw : 0 ≤ w) (hcut : (N : ℝ) < w ^ 6) :
    largeFifthPlusAttachment N cap w L X (receiverTest N)
      fifth.selectedAfter p = 0 := by
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
  unfold largeFifthPlusAttachment
  apply Finset.sum_eq_zero
  intro a ha
  have hidx : X ^ 5 < a ^ 5 * fifth.selectedAfter.prod ^ 6 := by
    change a ∈ (actualSmallRosserSupport N cap w).filter
      (fun a => X ^ 5 < a ^ 5 * fifth.selectedAfter.prod ^ 6) at ha
    exact (Finset.mem_filter.mp ha).2
  have haPos : 0 < a := by
    by_contra h
    have hazero : a = 0 := Nat.eq_zero_of_not_pos h
    simp [hazero] at hidx
  have hlarge : N < a * (p :: fifth.selectedAfter).prod :=
    six_rough_full_modulus_gt_N N a p fifth.selectedAfter w
      hw hlen hlo haPos hcut
  have hz : receiverTest N (a * (p :: fifth.selectedAfter).prod) = 0 :=
    receiverTest_zero_of_modulus_gt_N N _ hlarge
  simp [P4AOriginalFull87PhysicalHighQOwnedInvoice.highQTest, hz]

/-- On the original fixed receiver-generated stopped event population,
the signed fifth-to-sixth difference is zero under the literal six-factor
cutoff, for ANY N, cap, remaining order and signed fifth-event masses. -/
theorem actual_fixed_fifth_receiver_zero_of_six_cutoff
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ)
    (hw : 0 ≤ w) (hcut : (N : ℝ) < w ^ 6) :
    actualFixedSignedFifthTail delta n e q om N cap w z L X
      (receiverTest N) = 0 := by
  let events : FirstExitDepthState ℕ →
      List (FifthSixthStoppedEvent ℕ) :=
    fun state => actualFifthSixthWithoutBoth
      delta n e q om N cap w L X (receiverTest N) state
  have hevent (state : FirstExitDepthState ℕ)
      (hs : state ∈ sharedRankFour e q om N cap w z)
      (ev : FifthSixthStoppedEvent ℕ) (hev : ev ∈ events state) :
      commonSignedEventValue N cap w L X (receiverTest N) ev = 0 := by
    cases ev with
    | fifthExclusive fifth =>
        have hkernel : commonLargeSixthKernel N cap w L X
            (receiverTest N) fifth = 0 := by
          unfold commonLargeSixthKernel
          have hmap :
              (fifth.remainingAfter.map (fun p =>
                signedTreeCoefficient true fifth.massAfter *
                  largeFifthPlusAttachment N cap w L X
                    (receiverTest N) fifth.selectedAfter p)) =
                fifth.remainingAfter.map (fun _ => (0 : ℝ)) := by
            apply List.map_congr_left
            intro p hp
            rw [actual_fifth_receiver_plus_zero_of_six_cutoff
              delta n e q om N cap w z L X state hs fifth hev
              p hp hw hcut]
            simp
          rw [hmap]
          simp
        cases hk : fifth.kind <;>
          simp [commonSignedEventValue, hk, hkernel]
    | sixthFromBoth pre fifth =>
        simp [commonSignedEventValue]
  change ((sharedRankFour e q om N cap w z).map (fun state =>
    (((events state).map
      (commonSignedEventValue N cap w L X (receiverTest N))).sum))).sum = 0
  have houter :
      (sharedRankFour e q om N cap w z).map (fun state =>
        (((events state).map
          (commonSignedEventValue N cap w L X (receiverTest N))).sum)) =
      (sharedRankFour e q om N cap w z).map (fun _ => (0 : ℝ)) := by
    apply List.map_congr_left
    intro state hs
    have hinner :
        (events state).map
          (commonSignedEventValue N cap w L X (receiverTest N)) =
        (events state).map (fun _ => (0 : ℝ)) := by
      apply List.map_congr_left
      intro ev hev
      exact hevent state hs ev hev
    rw [hinner]
    simp
  rw [houter]
  simp

/-- The frozen UPPER numerical exponent kills the entire original
stopped receiver tail, not only the exceptional centre-prime correction.
This remains an instance at the LITERAL w argument, not a high-level
producer callsite theorem for generic w. -/
theorem actual_upper_rho0_stopped_receiver_zero
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (z L : ℝ) (X : ℕ) (hN : 8 ≤ N) :
    actualFixedSignedFifthTail delta n e q om N cap
      ((N : ℝ) ^ ((19 : ℝ) / 96)) z L X
      (receiverTest N) = 0 := by
  exact actual_fixed_fifth_receiver_zero_of_six_cutoff
    delta n e q om N cap ((N : ℝ) ^ ((19 : ℝ) / 96))
    z L X (by positivity) (upper_rho0_six_power_gt_N N hN)

/-- Consequently the literal-upper stopped RAW/LICENSED receiver
difference has no sixth contribution. The original strict X and epsilon
hypotheses are kept, not weakened or retuned. -/
theorem actual_upper_rho0_stopped_receiver_raw_eq_licensed
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (z : ℝ)
    (he : (0 : ℝ) ≤
      ((P4AOriginalCompleteSixthChronology.data e q om).e : ℝ))
    (hN : 8 ≤ N)
    (epsilon : ℝ) (heps : epsilon ≤ (1 / 500 : ℝ))
    (X : ℕ) (hX : (N : ℝ) ^ (3 / 5 : ℝ) ≤ (X : ℝ)) :
    rawStopped e q om N cap
      ((N : ℝ) ^ ((19 : ℝ) / 96)) z ((N : ℝ) ^ epsilon) X
        (receiverTest N) =
      licensedStopped delta n e q om N cap
        ((N : ℝ) ^ ((19 : ℝ) / 96)) z
          ((N : ℝ) ^ epsilon) X (receiverTest N) := by
  have hN1 : (1 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 1 < N by omega)
  have hdifference :=
    actual_stopped_difference_eq_common_signed_sixth_kernel
      delta n e q om N cap ((N : ℝ) ^ ((19 : ℝ) / 96)) z
      he hN1 epsilon heps X hX (receiverTest N)
  have hzero := actual_upper_rho0_stopped_receiver_zero
    delta n e q om N cap z ((N : ℝ) ^ epsilon) X hN
  change rawStopped e q om N cap
      ((N : ℝ) ^ ((19 : ℝ) / 96)) z ((N : ℝ) ^ epsilon) X
        (receiverTest N) -
      licensedStopped delta n e q om N cap
        ((N : ℝ) ^ ((19 : ℝ) / 96)) z
          ((N : ℝ) ^ epsilon) X (receiverTest N) =
      actualFixedSignedFifthTail delta n e q om N cap
        ((N : ℝ) ^ ((19 : ℝ) / 96)) z ((N : ℝ) ^ epsilon) X
          (receiverTest N) at hdifference
  rw [hzero] at hdifference
  linarith

end
end ImbalancedChen.P4AOriginalFull87UpperRho0SixReceiver
