import ImbalancedChen.P4AOriginalFull87BetaMassEnvelope
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

Return from the pointwise absolute primitive AP jump invoices to the
SIGNED primitive carrier discrepancy of the ORIGINAL full-modulus
PLUS-Rosser quotient room. This is essential for comparison with the
manuscript's signed prime-product distribution interface: its signed
coefficient estimate does NOT imply the previous per-modulus absolute
jump hypothesis.

All fifth raw/licensed signs and all ordered sixth occurrences remain
unchanged. The actual sharedRankFour producer and frozen survivor
selector are reused. We prove an exact finite identity only: no
distribution estimate, correct AP mean, coefficient-class admission,
or H_N payment is asserted by this source.
-/

namespace ImbalancedChen.P4AOriginalFull87SignedCarrierAP
noncomputable section
open scoped Classical BigOperators

open P4AOriginalFull87ActualPrimitiveRosserRoom (actualPrimitiveRosserRoom)
open P4AOriginalFull87ReflectedPrefixAbel
  (actualRoomBetaWeight reflectedPrimeStep actual_room_reflected_prime_abel
   frozenSurvivorSignedAbelPrimeRoom physical_after_lower_eq_original_reflected_abel)
open P4AOriginalFull87CentreIntervalBridge
  (originalCarrierReflectedStep original_reflected_step_eq_carrier_add_centre)
open P4AOriginalFull87WeightedCentreCancellation
  (original_room_weight_centre_step_zero
   original_room_abel_eq_carrier_jump_correction
   originalRoomCarrierJumpCorrection)
open P4AOriginalFull87CarrierGlobalJumpInvoice
  (originalCarrierJumpEvent frozenSurvivorCarrierJumpRoom
   frozenSurvivorCarrierMeanRoom frozen_abel_eq_mean_plus_carrier_jump)
open P4AOriginalFull87FifthSixthStoppedEvents (FifthSixthStoppedEvent)
open P4AOriginalFull87RankFourStoppedLocalization (sharedRankFour)
open P4AOriginalFull87SixthBothInvoice (actualFifthSixthWithoutBoth)
open P4AOriginalFull87FrozenSurvivorInvoice (keepFrozenUpperSurvivor)
open P4AOriginalFull87EighthPrimeMeanLedger (receiverTest)
open P4AOriginalFull87EarlyStopPhysicalGap (rawStopped licensedStopped)
open P4AOriginalFull87FifthSignedPrimitive (actualFixedSignedFifthTail)
open P4AOriginalFull87StoppedUpperHalfPrimeDirect (lowerHalfReceiver)

/-- An exact signed discrepancy on the ORIGINAL primitive PLUS-beta room.
The reference mean is still an arbitrary function of the COMPLETE
modulus b=(p::pre).prod; it is not yet certified as the manuscript's
same-rho AP density. In particular, this retains beta's sign. -/
def originalSignedPrimitiveCarrierAPDiscrepancy
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (pre : List ℕ)
    (p : ℕ) (mean : ℕ → ℝ) : ℝ :=
  ∑ a ∈ actualPrimitiveRosserRoom N cap w L X pre p,
    actualSmallRosserPlus N cap w L a *
      (originalCarrierReflectedStep N pre p a - mean (p :: pre).prod)

/-- A genuine room quotient is weighted only at coprime products.
The weighted centre correction therefore vanishes POINTWISE on
this room, not on arbitrary unweighted AP prefixes. -/
private theorem room_beta_carrier_eq_full_prime
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (pre : List ℕ)
    (p a : ℕ)
    (ha : a ∈ actualPrimitiveRosserRoom N cap w L X pre p) :
    actualSmallRosserPlus N cap w L a *
        originalCarrierReflectedStep N pre p a =
      actualSmallRosserPlus N cap w L a *
        reflectedPrimeStep N pre p a := by
  have hz :
      actualSmallRosserPlus N cap w L a *
        P4AOriginalFull87CentreIntervalBridge.originalCentreReflectedStep
          N pre p a = 0 := by
    simpa only [actualRoomBetaWeight, if_pos ha] using
      (original_room_weight_centre_step_zero N cap w L X pre p a)
  calc
    actualSmallRosserPlus N cap w L a *
        originalCarrierReflectedStep N pre p a =
      actualSmallRosserPlus N cap w L a *
        originalCarrierReflectedStep N pre p a +
      actualSmallRosserPlus N cap w L a *
        P4AOriginalFull87CentreIntervalBridge.originalCentreReflectedStep
          N pre p a := by rw [hz]; ring
    _ = actualSmallRosserPlus N cap w L a *
        reflectedPrimeStep N pre p a := by
      rw [original_reflected_step_eq_carrier_add_centre]
      ring

/-- This is a genuinely SIGNED, finite arithmetic equality, prior to
any per-modulus absolute values. The centre prime term is eliminated
only with the original beta and exact full-modulus coprimality. -/
theorem original_signed_primitive_carrier_AP_eq_jump
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (pre : List ℕ)
    (p : ℕ) (mean : ℕ → ℝ) :
    originalSignedPrimitiveCarrierAPDiscrepancy
      N cap w L X pre p mean =
      originalRoomCarrierJumpCorrection N cap w L X pre p mean := by
  classical
  let room := actualPrimitiveRosserRoom N cap w L X pre p
  let beta := actualSmallRosserPlus N cap w L
  let mu := mean (p :: pre).prod
  have hprime :
      (∑ a ∈ room,
        beta a * originalCarrierReflectedStep N pre p a) =
      ∑ a ∈ room.filter
        (fun a => N - a * (p :: pre).prod ∈ chenPrimePrefix N),
        beta a := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a ha
    rw [room_beta_carrier_eq_full_prime N cap w L X pre p a ha]
    by_cases hp : N - a * (p :: pre).prod ∈ chenPrimePrefix N
    · simp [reflectedPrimeStep, hp]
    · simp [reflectedPrimeStep, hp]
  have hlinear :
      (∑ a ∈ room,
        beta a * (originalCarrierReflectedStep N pre p a - mu)) =
      (∑ a ∈ room,
        beta a * originalCarrierReflectedStep N pre p a) -
        mu * (∑ a ∈ room, beta a) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
    ring
  have habel := actual_room_reflected_prime_abel
    N cap w L X pre p mean
  unfold originalSignedPrimitiveCarrierAPDiscrepancy
  change (∑ a ∈ room,
      beta a * (originalCarrierReflectedStep N pre p a - mu)) =
    originalRoomCarrierJumpCorrection N cap w L X pre p mean
  rw [hlinear, hprime, habel]
  rw [original_room_abel_eq_carrier_jump_correction]
  ring

/-- Signed primitive carrier AP discrepancy with the ORIGINAL
fifth RAW-only/LICENSED-only sign and the ordered sixth suffix. This
is not an absolute sum and cannot be bounded by the manuscript's PP
input until its coefficient-class/mean/weight normalizations match. -/
def originalSignedPrimitiveCarrierAPEvent
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (mean : ℕ → ℝ) :
    FifthSixthStoppedEvent ℕ → ℝ
  | .fifthExclusive fifth =>
      let v : ℝ := (fifth.remainingAfter.map (fun p =>
        signedTreeCoefficient true fifth.massAfter *
          originalSignedPrimitiveCarrierAPDiscrepancy N cap w L X
            fifth.selectedAfter p mean)).sum
      match fifth.kind with
      | .rawOnly => v
      | .licensedOnly => -v
      | .both => 0
  | .sixthFromBoth _ _ => 0

/-- The signed primitive AP account and the Abel-jump account agree
for each actual stopped event, including the original zero BOTH cases.
No occurrence or fifth-history mask is introduced here. -/
theorem original_signed_carrier_event_eq_jump_event
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (mean : ℕ → ℝ)
    (ev : FifthSixthStoppedEvent ℕ) :
    originalSignedPrimitiveCarrierAPEvent N cap w L X mean ev =
      originalCarrierJumpEvent N cap w L X mean ev := by
  classical
  cases ev with
  | sixthFromBoth pre fifth =>
      simp [originalSignedPrimitiveCarrierAPEvent, originalCarrierJumpEvent]
  | fifthExclusive fifth =>
      let c : ℝ := signedTreeCoefficient true fifth.massAfter
      let A : ℕ → ℝ := fun p =>
        originalSignedPrimitiveCarrierAPDiscrepancy
          N cap w L X fifth.selectedAfter p mean
      let J : ℕ → ℝ := fun p =>
        originalRoomCarrierJumpCorrection
          N cap w L X fifth.selectedAfter p mean
      have heq :
          (fifth.remainingAfter.map (fun p => c * A p)).sum =
          (fifth.remainingAfter.map (fun p => c * J p)).sum := by
        apply congrArg List.sum
        apply List.map_congr_left
        intro p hp
        dsimp [A, J]
        rw [original_signed_primitive_carrier_AP_eq_jump]
      cases hk : fifth.kind with
      | rawOnly =>
          simpa [originalSignedPrimitiveCarrierAPEvent,
            originalCarrierJumpEvent, hk, c, A, J] using heq
      | licensedOnly =>
          simpa [originalSignedPrimitiveCarrierAPEvent,
            originalCarrierJumpEvent, hk, c, A, J] using congrArg (fun x : ℝ => -x) heq
      | both =>
          simp [originalSignedPrimitiveCarrierAPEvent,
            originalCarrierJumpEvent, hk]

/-- Exactly the existing frozen sharedRankFour states, genuine original
fifth/sixth event Lists, frozen survivor selector and occurrence counts.
There is no new tree or surrogate source. -/
def frozenSurvivorSignedPrimitiveCarrierAPRoom
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w epsilon : ℝ) (X : ℕ)
    (mean : ℕ → ℝ) : ℝ :=
  ((sharedRankFour e q om N cap w
    ((N : ℝ) ^ ((19 : ℝ) / 96))).map (fun state =>
    (((actualFifthSixthWithoutBoth delta n e q om N cap w
      ((N : ℝ) ^ epsilon) X (receiverTest N) state).filter
        (keepFrozenUpperSurvivor N ((N : ℝ) ^ ((19 : ℝ) / 96))
          ((N : ℝ) ^ epsilon) X)).map
      (originalSignedPrimitiveCarrierAPEvent N cap w
        ((N : ℝ) ^ epsilon) X mean)).sum)).sum

theorem frozen_signed_primitive_carrier_AP_eq_jump
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w epsilon : ℝ) (X : ℕ)
    (mean : ℕ → ℝ) :
    frozenSurvivorSignedPrimitiveCarrierAPRoom
      delta n e q om N cap w epsilon X mean =
    frozenSurvivorCarrierJumpRoom
      delta n e q om N cap w epsilon X mean := by
  let states := sharedRankFour e q om N cap w
    ((N : ℝ) ^ ((19 : ℝ) / 96))
  let events := fun state =>
    (actualFifthSixthWithoutBoth delta n e q om N cap w
      ((N : ℝ) ^ epsilon) X (receiverTest N) state).filter
      (keepFrozenUpperSurvivor N ((N : ℝ) ^ ((19 : ℝ) / 96))
        ((N : ℝ) ^ epsilon) X)
  let A := originalSignedPrimitiveCarrierAPEvent
    N cap w ((N : ℝ) ^ epsilon) X mean
  let J := originalCarrierJumpEvent
    N cap w ((N : ℝ) ^ epsilon) X mean
  change (states.map (fun s => ((events s).map A).sum)).sum =
    (states.map (fun s => ((events s).map J).sum)).sum
  apply congrArg List.sum
  apply List.map_congr_left
  intro state hs
  apply congrArg List.sum
  apply List.map_congr_left
  intro ev hev
  exact original_signed_carrier_event_eq_jump_event
    N cap w ((N : ℝ) ^ epsilon) X mean ev

/-- Finite physical return to a SIGNED primitive-carrier discrepancy.
The lower-half receiver has been removed ONCE. Crucially, the
manuscript's signed PP estimate is not yet installed: this theorem
only identifies the exact arithmetic expression it would have to
control, including its original beta weights and list multiplicities. -/
theorem physical_after_lower_eq_mean_plus_signed_carrier_AP
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
    frozenSurvivorSignedPrimitiveCarrierAPRoom
      delta n e q om N cap w epsilon X mean := by
  calc
    _ = frozenSurvivorSignedAbelPrimeRoom
      delta n e q om N cap w epsilon X mean :=
        physical_after_lower_eq_original_reflected_abel
          delta n e q om N cap w epsilon X mean he hN heps hX
    _ = frozenSurvivorCarrierMeanRoom
        delta n e q om N cap w epsilon X mean +
      frozenSurvivorCarrierJumpRoom
        delta n e q om N cap w epsilon X mean :=
          frozen_abel_eq_mean_plus_carrier_jump
            delta n e q om N cap w epsilon X mean
    _ = _ := by rw [frozen_signed_primitive_carrier_AP_eq_jump]

end
end ImbalancedChen.P4AOriginalFull87SignedCarrierAP
