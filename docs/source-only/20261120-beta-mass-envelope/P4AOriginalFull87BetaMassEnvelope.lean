import ImbalancedChen.P4AOriginalFull87CarrierGlobalJumpInvoice
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

A finite, unconditional replacement for a separate Rosser-beta total-variation
estimate: on the ORIGINAL strict bounded full-modulus quotient room, variation
of the zero-extended beta weight is at most twice its exact absolute mass.
The actual primitive AP error is still an explicit, UNVERIFIED input on the
true nonzero beta jumps. Carry this inequality through the ORIGINAL frozen
rank-four states, fifth sign, ordered sixth occurrences and physical stopped
ledger, without altering any survivor filter, cap or lower-half payment.

This is a potentially coarser bill, not a proof of o(H_N), a density theorem,
or a claim that the AP estimate can be verified for the actual rho.
-/

namespace ImbalancedChen.P4AOriginalFull87BetaMassEnvelope
noncomputable section
open scoped Classical BigOperators

open P4AOriginalFull87CarrierGlobalJumpInvoice
  (originalCarrierJumpExactBill originalCarrierJumpEventBill
   frozenSurvivorCarrierJumpInvoice frozenSurvivorCarrierMeanRoom
   physical_after_lower_error_le_exact_carrier_invoice)
open P4AOriginalFull87ReflectedPrefixAbel (actualRoomBetaWeight)
open P4AOriginalFull87ActualPrimitiveRosserRoom (actualPrimitiveRosserRoom)
open P4AOriginalFull87CentreIntervalBridge (originalCarrierIntervalDiscrepancy)
open P4AOriginalFull87AnchoredJumpPrimitivePrefix (originalFullRoomLowerGate)
open P4AOriginalFull87FifthSixthStoppedEvents (FifthSixthStoppedEvent)
open P4AOriginalFull87RankFourStoppedLocalization (sharedRankFour)
open P4AOriginalFull87SixthBothInvoice (actualFifthSixthWithoutBoth)
open P4AOriginalFull87FrozenSurvivorInvoice (keepFrozenUpperSurvivor)
open P4AOriginalFull87EighthPrimeMeanLedger (receiverTest)
open P4AOriginalFull87EarlyStopPhysicalGap (rawStopped licensedStopped)
open P4AOriginalFull87FifthSignedPrimitive (actualFixedSignedFifthTail)
open P4AOriginalFull87StoppedUpperHalfPrimeDirect (lowerHalfReceiver)

/-- Balance of shifted absolute sums on the actual finite range. -/
private theorem abs_shift_balance (v : ℕ → ℝ) (m : ℕ) :
    (∑ t ∈ Finset.range m, |v (t + 1)|) + |v 0| =
      (∑ t ∈ Finset.range m, |v t|) + |v m| := by
  induction m with
  | zero => simp
  | succ m ih =>
      simp only [Finset.sum_range_succ]
      linarith

/-- For any finitely supported weight whose RIGHT endpoint is zero,
the exact finite jump variation costs at most twice its absolute mass.
No monotonicity or fixed-sign assumption is needed. -/
private theorem finite_variation_le_twice_mass
    (v : ℕ → ℝ) (m : ℕ) (hend : v m = 0) :
    (∑ t ∈ Finset.range m, |v t - v (t + 1)|) ≤
      2 * (∑ t ∈ Finset.range m, |v t|) := by
  have hshift := abs_shift_balance v m
  rw [hend] at hshift
  simp only [abs_zero, add_zero] at hshift
  have hlead :
      (∑ t ∈ Finset.range m, |v (t + 1)|) ≤
        ∑ t ∈ Finset.range m, |v t| := by
    linarith [abs_nonneg (v 0)]
  calc
    (∑ t ∈ Finset.range m, |v t - v (t + 1)|) ≤
        ∑ t ∈ Finset.range m, (|v t| + |v (t + 1)|) := by
          apply Finset.sum_le_sum
          intro t ht
          simpa only [sub_eq_add_neg, abs_neg] using
            (abs_add_le (v t) (-(v (t + 1))))
    _ = (∑ t ∈ Finset.range m, |v t|) +
        (∑ t ∈ Finset.range m, |v (t + 1)|) := Finset.sum_add_distrib
    _ ≤ 2 * (∑ t ∈ Finset.range m, |v t|) := by linarith

/-- Actual absolute PLUS-Rosser mass, with zero weight off the original
primitive quotient room. In particular, this is NOT the full interval
cardinality and does not replace the original coefficient by 1. -/
def originalRoomBetaRangeAbsMass
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (pre : List ℕ) (p : ℕ) : ℝ :=
  ∑ a ∈ Finset.range (N / (p :: pre).prod + 1),
    |actualRoomBetaWeight N cap w L X pre p a|

private theorem original_beta_terminal_zero
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (pre : List ℕ) (p : ℕ) :
    actualRoomBetaWeight N cap w L X pre p
      (N / (p :: pre).prod + 1) = 0 := by
  have hn : N / (p :: pre).prod + 1 ∉
      actualPrimitiveRosserRoom N cap w L X pre p := by
    intro ha
    have hfull := (Finset.mem_filter.mp ha).1
    change N / (p :: pre).prod + 1 ∈ Finset.Ico
      ((N / (2 * (p :: pre).prod) + 1).max
        (X / (p :: pre).prod + 1))
      ((Nat.ceil L).min (N / (p :: pre).prod + 1)) at hfull
    have hhi := (Finset.mem_Ico.mp hfull).2
    have hmin := min_le_right (Nat.ceil L) (N / (p :: pre).prod + 1)
    omega
  simp [actualRoomBetaWeight, hn]

/-- Real, ORIGINAL room variation has an unconditional absolute-mass
envelope. This eliminates an independently unquantified beta-variation
factor at the cost of a possible factor-two loss. -/
theorem original_actual_beta_variation_le_twice_mass
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (pre : List ℕ) (p : ℕ) :
    (∑ t ∈ Finset.range (N / (p :: pre).prod + 1),
      |actualRoomBetaWeight N cap w L X pre p t -
       actualRoomBetaWeight N cap w L X pre p (t + 1)|) ≤
      2 * originalRoomBetaRangeAbsMass N cap w L X pre p := by
  let v := actualRoomBetaWeight N cap w L X pre p
  let m := N / (p :: pre).prod + 1
  have hend : v m = 0 :=
    original_beta_terminal_zero N cap w L X pre p
  simpa only [originalRoomBetaRangeAbsMass, v, m] using
    finite_variation_le_twice_mass v m hend

/-- A LOCAL AP input only at genuine beta jumps, not at every integer
in the quotient interval. It is not supplied by this module and must be
authenticated from an external theorem for the same complete modulus. -/
theorem original_exact_carrier_bill_le_beta_mass_envelope
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (pre : List ℕ) (p : ℕ) (mean : ℕ → ℝ) (E : ℝ)
    (hE : 0 ≤ E)
    (hAP : ∀ t ∈ Finset.range (N / (p :: pre).prod + 1),
      actualRoomBetaWeight N cap w L X pre p t ≠
        actualRoomBetaWeight N cap w L X pre p (t + 1) →
      |originalCarrierIntervalDiscrepancy N pre p mean
        (originalFullRoomLowerGate N X pre p) (t + 1)| ≤ E) :
    originalCarrierJumpExactBill N cap w L X pre p mean ≤
      (2 * E) * originalRoomBetaRangeAbsMass N cap w L X pre p := by
  let v := actualRoomBetaWeight N cap w L X pre p
  let m := N / (p :: pre).prod + 1
  have hvar := original_actual_beta_variation_le_twice_mass
    N cap w L X pre p
  change (∑ t ∈ Finset.range m,
    |v t - v (t + 1)| *
      |originalCarrierIntervalDiscrepancy N pre p mean
        (originalFullRoomLowerGate N X pre p) (t + 1)|) ≤
    (2 * E) * originalRoomBetaRangeAbsMass N cap w L X pre p
  calc
    _ ≤ ∑ t ∈ Finset.range m, |v t - v (t + 1)| * E := by
      apply Finset.sum_le_sum
      intro t ht
      by_cases hj : v t = v (t + 1)
      · simp [hj]
      · exact mul_le_mul_of_nonneg_left
          (hAP t ht hj) (abs_nonneg (v t - v (t + 1)))
    _ = E * (∑ t ∈ Finset.range m, |v t - v (t + 1)|) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      ring
    _ ≤ E * (2 * originalRoomBetaRangeAbsMass N cap w L X pre p) := by
      exact mul_le_mul_of_nonneg_left hvar hE
    _ = (2 * E) * originalRoomBetaRangeAbsMass N cap w L X pre p := by ring

/-- The coarser AP envelope retains the ORIGINAL fifth signed coefficient,
actual sixth List occurrences, and the original BOTH-zero event behavior. -/
def originalCarrierMassAPEventBill
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (E : ℕ → ℝ) :
    FifthSixthStoppedEvent ℕ → ℝ
  | .fifthExclusive fifth =>
      let v : ℝ := (fifth.remainingAfter.map (fun p =>
        |signedTreeCoefficient true fifth.massAfter| *
          ((2 * E (p :: fifth.selectedAfter).prod) *
            originalRoomBetaRangeAbsMass N cap w L X
              fifth.selectedAfter p))).sum
      match fifth.kind with
      | .rawOnly | .licensedOnly => v
      | .both => 0
  | .sixthFromBoth _ _ => 0

private theorem list_map_sum_le {α : Type*} (xs : List α)
    (f g : α → ℝ) (h : ∀ x ∈ xs, f x ≤ g x) :
    (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      apply add_le_add (h x (by simp))
      apply ih
      intro y hy
      exact h y (by simp [hy])

theorem original_carrier_event_bill_le_mass_AP_bill
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (mean E : ℕ → ℝ)
    (hE : ∀ b, 0 ≤ E b)
    (hAP : ∀ (pre : List ℕ) (p t : ℕ),
      t ∈ Finset.range (N / (p :: pre).prod + 1) →
      actualRoomBetaWeight N cap w L X pre p t ≠
        actualRoomBetaWeight N cap w L X pre p (t + 1) →
      |originalCarrierIntervalDiscrepancy N pre p mean
        (originalFullRoomLowerGate N X pre p) (t + 1)| ≤
          E (p :: pre).prod)
    (ev : FifthSixthStoppedEvent ℕ) :
    originalCarrierJumpEventBill N cap w L X mean ev ≤
      originalCarrierMassAPEventBill N cap w L X E ev := by
  classical
  cases ev with
  | sixthFromBoth pre fifth =>
      simp [originalCarrierJumpEventBill, originalCarrierMassAPEventBill]
  | fifthExclusive fifth =>
      let c : ℝ := signedTreeCoefficient true fifth.massAfter
      let F : ℕ → ℝ := fun p =>
        originalCarrierJumpExactBill N cap w L X fifth.selectedAfter p mean
      let G : ℕ → ℝ := fun p =>
        (2 * E (p :: fifth.selectedAfter).prod) *
          originalRoomBetaRangeAbsMass N cap w L X fifth.selectedAfter p
      have hsum :
          (fifth.remainingAfter.map (fun p => |c| * F p)).sum ≤
            (fifth.remainingAfter.map (fun p => |c| * G p)).sum := by
        apply list_map_sum_le
        intro p hp
        exact mul_le_mul_of_nonneg_left
          (original_exact_carrier_bill_le_beta_mass_envelope
            N cap w L X fifth.selectedAfter p mean
            (E (p :: fifth.selectedAfter).prod)
            (hE _) (hAP fifth.selectedAfter p))
          (abs_nonneg c)
      cases hk : fifth.kind with
      | rawOnly =>
          simpa [originalCarrierJumpEventBill,
            originalCarrierMassAPEventBill, hk, c, F, G] using hsum
      | licensedOnly =>
          simpa [originalCarrierJumpEventBill,
            originalCarrierMassAPEventBill, hk, c, F, G] using hsum
      | both =>
          simp [originalCarrierJumpEventBill, originalCarrierMassAPEventBill, hk]

/-- Same exact state/event producer and frozen filter as the existing
primitive-jump invoice; no new parent or alternative selection. -/
def frozenSurvivorCarrierMassAPInvoice
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w epsilon : ℝ) (X : ℕ)
    (E : ℕ → ℝ) : ℝ :=
  ((sharedRankFour e q om N cap w
    ((N : ℝ) ^ ((19 : ℝ) / 96))).map (fun state =>
    (((actualFifthSixthWithoutBoth delta n e q om N cap w
      ((N : ℝ) ^ epsilon) X (receiverTest N) state).filter
        (keepFrozenUpperSurvivor N ((N : ℝ) ^ ((19 : ℝ) / 96))
          ((N : ℝ) ^ epsilon) X)).map
      (originalCarrierMassAPEventBill N cap w
        ((N : ℝ) ^ epsilon) X E)).sum)).sum

theorem frozen_exact_jump_invoice_le_mass_AP_invoice
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w epsilon : ℝ) (X : ℕ)
    (mean E : ℕ → ℝ)
    (hE : ∀ b, 0 ≤ E b)
    (hAP : ∀ (pre : List ℕ) (p t : ℕ),
      t ∈ Finset.range (N / (p :: pre).prod + 1) →
      actualRoomBetaWeight N cap w ((N : ℝ) ^ epsilon) X pre p t ≠
        actualRoomBetaWeight N cap w ((N : ℝ) ^ epsilon) X pre p (t + 1) →
      |originalCarrierIntervalDiscrepancy N pre p mean
        (originalFullRoomLowerGate N X pre p) (t + 1)| ≤
          E (p :: pre).prod) :
    frozenSurvivorCarrierJumpInvoice
      delta n e q om N cap w epsilon X mean ≤
    frozenSurvivorCarrierMassAPInvoice
      delta n e q om N cap w epsilon X E := by
  let states := sharedRankFour e q om N cap w
    ((N : ℝ) ^ ((19 : ℝ) / 96))
  let events := fun state =>
    (actualFifthSixthWithoutBoth delta n e q om N cap w
      ((N : ℝ) ^ epsilon) X (receiverTest N) state).filter
      (keepFrozenUpperSurvivor N ((N : ℝ) ^ ((19 : ℝ) / 96))
        ((N : ℝ) ^ epsilon) X)
  let B := originalCarrierJumpEventBill
    N cap w ((N : ℝ) ^ epsilon) X mean
  let C := originalCarrierMassAPEventBill
    N cap w ((N : ℝ) ^ epsilon) X E
  change (states.map (fun s => ((events s).map B).sum)).sum ≤
    (states.map (fun s => ((events s).map C).sum)).sum
  apply list_map_sum_le
  intro state hs
  apply list_map_sum_le
  intro ev hev
  exact original_carrier_event_bill_le_mass_AP_bill
    N cap w ((N : ℝ) ^ epsilon) X mean E hE hAP ev

/-- Conditional physical accounting result. AP errors remain UNPROVED;
the coarser exact beta-mass bill is NOT a payment against H_N. -/
theorem physical_after_lower_error_le_beta_mass_AP_invoice
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w epsilon : ℝ) (X : ℕ)
    (mean E : ℕ → ℝ)
    (he : (0 : ℝ) ≤
      ((P4AOriginalCompleteSixthChronology.data e q om).e : ℝ))
    (hN : (1 : ℝ) < (N : ℝ))
    (heps : epsilon ≤ (1 / 500 : ℝ))
    (hX : (N : ℝ) ^ (3 / 5 : ℝ) ≤ (X : ℝ))
    (hE : ∀ b, 0 ≤ E b)
    (hAP : ∀ (pre : List ℕ) (p t : ℕ),
      t ∈ Finset.range (N / (p :: pre).prod + 1) →
      actualRoomBetaWeight N cap w ((N : ℝ) ^ epsilon) X pre p t ≠
        actualRoomBetaWeight N cap w ((N : ℝ) ^ epsilon) X pre p (t + 1) →
      |originalCarrierIntervalDiscrepancy N pre p mean
        (originalFullRoomLowerGate N X pre p) (t + 1)| ≤
          E (p :: pre).prod) :
    |((rawStopped e q om N cap w ((N : ℝ) ^ ((19 : ℝ) / 96))
         ((N : ℝ) ^ epsilon) X (receiverTest N) -
       licensedStopped delta n e q om N cap w
         ((N : ℝ) ^ ((19 : ℝ) / 96))
         ((N : ℝ) ^ epsilon) X (receiverTest N)) -
      actualFixedSignedFifthTail delta n e q om N cap w
        ((N : ℝ) ^ ((19 : ℝ) / 96))
        ((N : ℝ) ^ epsilon) X (lowerHalfReceiver N)) -
      frozenSurvivorCarrierMeanRoom
        delta n e q om N cap w epsilon X mean| ≤
    frozenSurvivorCarrierMassAPInvoice
      delta n e q om N cap w epsilon X E := by
  calc
    _ ≤ frozenSurvivorCarrierJumpInvoice
      delta n e q om N cap w epsilon X mean :=
        physical_after_lower_error_le_exact_carrier_invoice
          delta n e q om N cap w epsilon X mean he hN heps hX
    _ ≤ _ := frozen_exact_jump_invoice_le_mass_AP_invoice
      delta n e q om N cap w epsilon X mean E hE hAP

end
end ImbalancedChen.P4AOriginalFull87BetaMassEnvelope
