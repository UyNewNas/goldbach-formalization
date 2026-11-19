import ImbalancedChen.P4AOriginalFull87OneShellAPGap
import ImbalancedChen.ChenInitialPrimeSource
import Mathlib.Tactic

/-!
P1.4 SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

Continue the actual ONE-SHELL obstruction without discarding its signed
non-shell AP tail.  The AP tail at Q=a*b is *exactly* the actual prime
receiver's proper-divisor fibre: n=N-P, Q | n and Q < n.

This turns the outside-shell correction into a signed divisor convolution
over the ORIGINAL receiver n, preserving beta's sign and all original
ordered fifth/sixth occurrences.  It does NOT identify this correction
with the manuscript's smooth signed PP estimate, or bound it by o(H_N).
No changed or inherited branch receives an extra mask.
-/

namespace ImbalancedChen.P4AOriginalFull87ProperReceiverTail
noncomputable section
open scoped Classical BigOperators

open P4AOriginalFull87OneShellAPGap
  (actualFullQPrimitiveAPFibre actualFullQOutsideOneShell
   originalFullQOutsideShellRoom originalFullQOutsideShellEvent
   frozenFullQOutsideShellRoom
   frozenFullQPrimitiveAPRoom
   physical_after_lower_eq_mean_plus_full_AP_minus_shell_tail)
open P4AOriginalFull87ActualPrimitiveRosserRoom (actualPrimitiveRosserRoom)
open P4AOriginalFull87CarrierGlobalJumpInvoice (frozenSurvivorCarrierMeanRoom)
open P4AOriginalFull87FifthSixthStoppedEvents (FifthSixthStoppedEvent)
open P4AOriginalFull87RankFourStoppedLocalization (sharedRankFour)
open P4AOriginalFull87SixthBothInvoice (actualFifthSixthWithoutBoth)
open P4AOriginalFull87FrozenSurvivorInvoice (keepFrozenUpperSurvivor)
open P4AOriginalFull87EighthPrimeMeanLedger (receiverTest)
open P4AOriginalFull87EarlyStopPhysicalGap (rawStopped licensedStopped)
open P4AOriginalFull87FifthSignedPrimitive (actualFixedSignedFifthTail)
open P4AOriginalFull87StoppedUpperHalfPrimeDirect (lowerHalfReceiver)

/-- Proper multiples in the REAL receiver source, not a synthetic AP or
a q-dependent smooth cutoff. Both Q=0 and Q=1 retain their true semantics. -/
def actualFullQProperReceiverFibre (N Q : ℕ) : Finset ℕ :=
  (chenPrimeReceiverSource N).filter (fun r => Q ∣ r ∧ Q < r)

/-- The omitted AP shells correspond exactly to proper multiples Q|r,
Q<r of the SAME modulus in the real receiver image.  In particular,
the isolated shell r=Q is removed once, not all congruence-class primes. -/
theorem actual_proper_receiver_eq_outside_image (N Q : ℕ) :
    actualFullQProperReceiverFibre N Q =
      (actualFullQOutsideOneShell N Q).image (fun P => N - P) := by
  classical
  have hf :
      (chenAdditivePrimeCarrier N).filter
          (fun P => Q ∣ N - P ∧ Q < N - P) =
        actualFullQOutsideOneShell N Q := by
    ext P
    constructor
    · intro hx
      obtain ⟨hP, hdvd, hlt⟩ := Finset.mem_filter.mp hx
      have hPN : P ≤ N := (mem_chenAdditivePrimeCarrier.mp hP).1.le
      have hmod : Nat.ModEq Q P N :=
        (dvd_sub_iff_modEq_of_le hPN).mp hdvd
      apply Finset.mem_erase.mpr
      constructor
      · intro heq
        omega
      · exact Finset.mem_filter.mpr ⟨hP, hmod⟩
    · intro hx
      have hx' : P ∈
          (actualFullQPrimitiveAPFibre N Q).erase (N - Q) := hx
      obtain ⟨hne, hAP⟩ := Finset.mem_erase.mp hx'
      obtain ⟨hP, hmod⟩ := Finset.mem_filter.mp hAP
      have hPN : P < N := (mem_chenAdditivePrimeCarrier.mp hP).1
      have hdvd : Q ∣ N - P :=
        (dvd_sub_iff_modEq_of_le hPN.le).mpr hmod
      have hpos : 0 < N - P := by omega
      have hle : Q ≤ N - P := Nat.le_of_dvd hpos hdvd
      have hlt : Q < N - P := by
        by_contra hnot
        have heq : P = N - Q := by omega
        exact hne heq
      exact Finset.mem_filter.mpr ⟨hP, hdvd, hlt⟩
  unfold actualFullQProperReceiverFibre
  rw [chenPrimeReceiverSource_filter_eq_image, hf]

/-- Correct counting with occurrence labels intact: P ↦ N-P is
injective on the actual carrier. No prime is counted twice by shifting. -/
theorem outside_shell_card_eq_proper_receiver (N Q : ℕ) :
    ((actualFullQOutsideOneShell N Q).card : ℝ) =
      ((actualFullQProperReceiverFibre N Q).card : ℝ) := by
  classical
  have hcard : (actualFullQProperReceiverFibre N Q).card =
      (actualFullQOutsideOneShell N Q).card := by
    rw [actual_proper_receiver_eq_outside_image]
    apply Finset.card_image_of_injOn
    intro P hP R hR heq
    have hp : P ∈ chenAdditivePrimeCarrier N :=
      (Finset.mem_filter.mp (Finset.mem_erase.mp hP).2).1
    have hr : R ∈ chenAdditivePrimeCarrier N :=
      (Finset.mem_filter.mp (Finset.mem_erase.mp hR).2).1
    exact chenPrimeReceiverSource_shift_injective hp hr heq
  exact_mod_cast hcard.symm

/-- Every proper multiple is genuinely above Q but still in the
original receiver range. No large-modulus error is hidden by a mask. -/
theorem proper_receiver_fibre_data {N Q r : ℕ}
    (hr : r ∈ actualFullQProperReceiverFibre N Q) :
    Q ∣ r ∧ Q < r ∧ r ≤ N := by
  obtain ⟨hs, hq⟩ := Finset.mem_filter.mp hr
  exact ⟨hq.1, hq.2, (chenPrimeReceiverSource_data hs).2.1⟩

/-- Original signed PLUS-beta coefficients aggregated at a single REAL
receiver r.  This is an actual proper-divisor sum, not a new rho field.
The integer quotient a retains its original strict Rosser room. -/
def originalProperReceiverDivisorKernel
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (pre : List ℕ)
    (p r : ℕ) : ℝ :=
  ∑ a ∈ actualPrimitiveRosserRoom N cap w L X pre p,
    if a * (p :: pre).prod ∣ r ∧ a * (p :: pre).prod < r
    then actualSmallRosserPlus N cap w L a
    else 0

/-- Convolution over the actual N-P receiver list. Neither the
prime carrier nor a fifth/sixth occurrence is deduplicated. -/
def originalProperReceiverDivisorConvolution
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (pre : List ℕ)
    (p : ℕ) : ℝ :=
  ∑ r ∈ chenPrimeReceiverSource N,
    originalProperReceiverDivisorKernel N cap w L X pre p r

private theorem weight_times_proper_receiver_card
    (N Q : ℕ) (weight : ℝ) :
    weight * ((actualFullQProperReceiverFibre N Q).card : ℝ) =
      ∑ r ∈ chenPrimeReceiverSource N,
        if Q ∣ r ∧ Q < r then weight else 0 := by
  classical
  unfold actualFullQProperReceiverFibre
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  ring

/-- Main new finite transformation: sum_a beta(a) #outside(AP_{a*b})
equals sum_{actual r} sum_{a*b | r, a*b<r} beta(a).
No absolute values, fictitious smooth weight or PP assumption. -/
theorem original_outside_shell_eq_receiver_convolution
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (pre : List ℕ)
    (p : ℕ) :
    originalFullQOutsideShellRoom N cap w L X pre p =
      originalProperReceiverDivisorConvolution N cap w L X pre p := by
  classical
  unfold originalFullQOutsideShellRoom
    originalProperReceiverDivisorConvolution
    originalProperReceiverDivisorKernel
  calc
    (∑ a ∈ actualPrimitiveRosserRoom N cap w L X pre p,
      actualSmallRosserPlus N cap w L a *
        ((actualFullQOutsideOneShell N
          (a * (p :: pre).prod)).card : ℝ)) =
      ∑ a ∈ actualPrimitiveRosserRoom N cap w L X pre p,
        ∑ r ∈ chenPrimeReceiverSource N,
          if a * (p :: pre).prod ∣ r ∧ a * (p :: pre).prod < r
          then actualSmallRosserPlus N cap w L a else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [outside_shell_card_eq_proper_receiver]
      exact weight_times_proper_receiver_card N
        (a * (p :: pre).prod) (actualSmallRosserPlus N cap w L a)
    _ = _ := Finset.sum_comm

/-- Preserve the exact RAW-only/LICENSED-only sign and order of the
fifth.remainingAfter List, with BOTH and sixthFromBoth unchanged. -/
def originalProperReceiverConvolutionEvent
    (N cap : ℕ) (w L : ℝ) (X : ℕ) :
    FifthSixthStoppedEvent ℕ → ℝ
  | .fifthExclusive fifth =>
      let v : ℝ := (fifth.remainingAfter.map (fun p =>
        signedTreeCoefficient true fifth.massAfter *
          originalProperReceiverDivisorConvolution N cap w L X
            fifth.selectedAfter p)).sum
      match fifth.kind with
      | .rawOnly => v
      | .licensedOnly => -v
      | .both => 0
  | .sixthFromBoth _ _ => 0

theorem outside_shell_event_eq_receiver_convolution
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (ev : FifthSixthStoppedEvent ℕ) :
    originalFullQOutsideShellEvent N cap w L X ev =
      originalProperReceiverConvolutionEvent N cap w L X ev := by
  classical
  cases ev with
  | sixthFromBoth pre fifth =>
      rfl
  | fifthExclusive fifth =>
      cases hk : fifth.kind with
      | rawOnly =>
          simp [originalFullQOutsideShellEvent,
            originalProperReceiverConvolutionEvent, hk,
            original_outside_shell_eq_receiver_convolution]
      | licensedOnly =>
          simp [originalFullQOutsideShellEvent,
            originalProperReceiverConvolutionEvent, hk,
            original_outside_shell_eq_receiver_convolution]
      | both =>
          simp [originalFullQOutsideShellEvent,
            originalProperReceiverConvolutionEvent, hk]

/-- Same source, same actual sharedRankFour parent and survivor selector.
This is the receiver-coordinate invoice for ALL ordered occurrences. -/
def frozenProperReceiverConvolution
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w epsilon : ℝ) (X : ℕ) : ℝ :=
  ((sharedRankFour e q om N cap w
    ((N : ℝ) ^ ((19 : ℝ) / 96))).map (fun state =>
    (((actualFifthSixthWithoutBoth delta n e q om N cap w
      ((N : ℝ) ^ epsilon) X (receiverTest N) state).filter
        (keepFrozenUpperSurvivor N ((N : ℝ) ^ ((19 : ℝ) / 96))
          ((N : ℝ) ^ epsilon) X)).map
      (originalProperReceiverConvolutionEvent N cap w
        ((N : ℝ) ^ epsilon) X)).sum)).sum

theorem frozen_outside_shell_eq_receiver_convolution
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w epsilon : ℝ) (X : ℕ) :
    frozenFullQOutsideShellRoom delta n e q om N cap w epsilon X =
      frozenProperReceiverConvolution delta n e q om N cap w epsilon X := by
  let states := sharedRankFour e q om N cap w
    ((N : ℝ) ^ ((19 : ℝ) / 96))
  let events := fun state =>
    (actualFifthSixthWithoutBoth delta n e q om N cap w
      ((N : ℝ) ^ epsilon) X (receiverTest N) state).filter
      (keepFrozenUpperSurvivor N ((N : ℝ) ^ ((19 : ℝ) / 96))
        ((N : ℝ) ^ epsilon) X)
  change (states.map (fun s => ((events s).map
    (originalFullQOutsideShellEvent N cap w ((N : ℝ) ^ epsilon) X)).sum)).sum =
    (states.map (fun s => ((events s).map
    (originalProperReceiverConvolutionEvent N cap w
      ((N : ℝ) ^ epsilon) X)).sum)).sum
  apply congrArg List.sum
  apply List.map_congr_left
  intro state hs
  apply congrArg List.sum
  apply List.map_congr_left
  intro ev hev
  exact outside_shell_event_eq_receiver_convolution
    N cap w ((N : ℝ) ^ epsilon) X ev

/-- Actual stopped physical difference with the lower receiver paid
ONCE, now exposing the exact signed proper-divisor convolution.
This has not yet been estimated relative to H_N. -/
theorem physical_after_lower_eq_mean_plus_full_AP_minus_proper_divisors
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w epsilon : ℝ) (X : ℕ)
    (mean : ℕ → ℝ)
    (he : (0 : ℝ) ≤
      ((P4AOriginalCompleteSixthChronology.data e q om).e : ℝ))
    (hN : (1 : ℝ) < (N : ℝ))
    (heps : epsilon ≤ (1 / 500 : ℝ))
    (hX : (N : ℝ) ^ (3 / 5 : ℝ) ≤ (X : ℝ)) :
    (rawStopped e q om N cap w ((N : ℝ) ^ ((19 : ℝ) / 96))
        ((N : ℝ) ^ epsilon) X (receiverTest N) -
      licensedStopped delta n e q om N cap w
        ((N : ℝ) ^ ((19 : ℝ) / 96))
        ((N : ℝ) ^ epsilon) X (receiverTest N)) -
      actualFixedSignedFifthTail delta n e q om N cap w
        ((N : ℝ) ^ ((19 : ℝ) / 96))
        ((N : ℝ) ^ epsilon) X (lowerHalfReceiver N) =
    frozenSurvivorCarrierMeanRoom
      delta n e q om N cap w epsilon X mean +
    frozenFullQPrimitiveAPRoom
      delta n e q om N cap w epsilon X mean -
    frozenProperReceiverConvolution
      delta n e q om N cap w epsilon X := by
  rw [physical_after_lower_eq_mean_plus_full_AP_minus_shell_tail
    delta n e q om N cap w epsilon X mean he hN heps hX]
  rw [frozen_outside_shell_eq_receiver_convolution]

end
end ImbalancedChen.P4AOriginalFull87ProperReceiverTail
