import ImbalancedChen.P4AOriginalFull87RankSevenStoppedHighQ
import ImbalancedChen.P4AOriginalFull87FifthSixthStoppedEvents
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

At the actual shared rank-four parent, both-admitted fifth children are
expanded at the genuine sixth gate. This packet removes only the sixth-BOTH
events: their raw-minus-licensed stopped-before-eight value is zero at high-q
by the original rank-seven calculation. Fifth-only and sixth-only descendants
are preserved with their original signed stopped subtree, carrier suffix,
history, mass and List occurrence. This is an exact local invoice refinement,
not the assertion that the whole stopped delta vanishes.
-/

namespace ImbalancedChen.P4AOriginalFull87SixthBothInvoice
noncomputable section
open scoped Classical BigOperators
open P1Pair12RetainedSignedSource (stoppedTest attachedLeafTest)
open P4AOriginalFull87FirstFifthStoppedEvents
  (FifthStoppedEvent FifthAdmissionClass firstFifthEvents)
open P4AOriginalFull87FifthSixthStoppedEvents
  (FifthSixthStoppedEvent fifthThenSixthEvents
   actualFifthSixthEvents actual_stopped_difference_eq_fifth_sixth_events)
open P4AOriginalFull87RankSevenStoppedHighQ
  (actual_rank_six_stopped_difference_zero_at_highq)
open P4AOriginalFull87RankFourStoppedLocalization (sharedRankFour)
open P4AOriginalFull87EarlyStopPhysicalGap
  (rawStopped licensedStopped
   abs_actual_full_physical_difference_le_stop_and_five_leaf_classes)
open P4AOriginalFull87PhysicalHighQOwnedInvoice (highQTest)
open P4AOriginalFull87RawTrimSignedHighQ (rawOutsideHighQInvoice)
open P4AOriginalFull87LicensedOutsideThreeInvoices (licensedOutsideHighQInvoice)
open P4AOriginalFull87ThreeClassLeafInvoices (actualProducerThreeClassLeafBill)

/-- Only the original sixth admission whose TWO producer policies agree is
discarded. Fifth-exclusive and sixth-exclusive events are never filtered.
Each retained event keeps its original stoppedTest value and occurrence. -/
def fifthSixthWithoutBoth {α : Type*}
    (R S : Bool → List α → Bool) (h : α → ℝ)
    (T : Bool → List α → ℝ)
    (pre : List α) (positive : Bool) (mass : ℝ) :
    List α → List (FifthSixthStoppedEvent α)
  | [] => []
  | p :: ps =>
      let child := p :: pre
      let sign := !positive
      let childMass := mass * h p
      let rawChild := stoppedTest 8 R h T child sign childMass ps
      let licChild := stoppedTest 8 S h T child sign childMass ps
      let emit (kind : FifthAdmissionClass) (value : ℝ) :
          List (FifthSixthStoppedEvent α) :=
        [.fifthExclusive ⟨child, sign, childMass, ps, kind, value⟩]
      let now :=
        if R sign child = true then
          if S sign child = true then
            ((firstFifthEvents R S h T child sign childMass ps).filter
              (fun ev => decide (ev.kind ≠ .both))).map
                (FifthSixthStoppedEvent.sixthFromBoth child)
          else emit .rawOnly rawChild
        else if S sign child = true then
          emit .licensedOnly (-licChild)
        else []
      now ++ fifthSixthWithoutBoth R S h T pre positive mass ps

/-- Finite carrier conservation: removing BOTH-tagged sixth events is valid
only after proving that their literal raw-minus-licensed stopped value is
zero for every actual sixth candidate, with its OWN post-candidate suffix.
The statement is parametrised by g so both signed and absolute invoices
are covered by exactly the same finite argument. -/
private theorem firstFifthEvents_map_sum_drop_both
    {α : Type*} (R S : Bool → List α → Bool)
    (h : α → ℝ) (T : Bool → List α → ℝ)
    (pre : List α) (positive : Bool) (mass : ℝ)
    (remaining : List α) (g : ℝ → ℝ) (hg : g 0 = 0)
    (hcancel : ∀ p tail,
      stoppedTest 8 R h T (p :: pre) (!positive)
        (mass * h p) tail =
      stoppedTest 8 S h T (p :: pre) (!positive)
        (mass * h p) tail) :
    ((firstFifthEvents R S h T pre positive mass remaining).map
      (fun ev => g ev.signedValue)).sum =
    (((firstFifthEvents R S h T pre positive mass remaining).filter
      (fun ev => decide (ev.kind ≠ .both))).map
      (fun ev => g ev.signedValue)).sum := by
  induction remaining with
  | nil =>
      simp [firstFifthEvents]
  | cons p ps ih =>
      by_cases hr : R (!positive) (p :: pre) = true
      · by_cases hs : S (!positive) (p :: pre) = true
        · have hval : stoppedTest 8 R h T (p :: pre) (!positive)
              (mass * h p) ps -
            stoppedTest 8 S h T (p :: pre) (!positive)
              (mass * h p) ps = 0 :=
            sub_eq_zero.mpr (hcancel p ps)
          simp [firstFifthEvents, hr, hs, hval, hg, ih,
            List.filter_append, List.map_append, List.sum_append]
        · simp [firstFifthEvents, hr, hs, ih,
            List.filter_append, List.map_append, List.sum_append]
      · by_cases hs : S (!positive) (p :: pre) = true
        · simp [firstFifthEvents, hr, hs, ih,
            List.filter_append, List.map_append, List.sum_append]
        · simp [firstFifthEvents, hr, hs, ih,
            List.filter_append, List.map_append, List.sum_append]

/-- A single generic proof of conservation from the fifth gate to its real
sixth gate. The cancelled sixth-BOTH subtree is a proved ZERO, not a
parameter supplied as a smallness claim for the entire stopped difference. -/
private theorem fifthThenSixth_map_sum_drop_both
    {α : Type*} (R S : Bool → List α → Bool)
    (h : α → ℝ) (T : Bool → List α → ℝ)
    (pre : List α) (positive : Bool) (mass : ℝ)
    (remaining : List α) (g : ℝ → ℝ) (hg : g 0 = 0)
    (hcancel : ∀ p q tail,
      stoppedTest 8 R h T (q :: p :: pre) (!(!positive))
        ((mass * h p) * h q) tail =
      stoppedTest 8 S h T (q :: p :: pre) (!(!positive))
        ((mass * h p) * h q) tail) :
    ((fifthThenSixthEvents R S h T pre positive mass remaining).map
      (fun ev => g ev.signedValue)).sum =
    ((fifthSixthWithoutBoth R S h T pre positive mass remaining).map
      (fun ev => g ev.signedValue)).sum := by
  induction remaining with
  | nil =>
      simp [fifthThenSixthEvents, fifthSixthWithoutBoth]
  | cons p ps ih =>
      have hinner := firstFifthEvents_map_sum_drop_both
        R S h T (p :: pre) (!positive) (mass * h p)
        ps g hg (by
          intro q tail
          exact hcancel p q tail)
      by_cases hr : R (!positive) (p :: pre) = true
      · by_cases hs : S (!positive) (p :: pre) = true
        · simp [fifthThenSixthEvents, fifthSixthWithoutBoth,
            hr, hs, List.map_append, List.map_map,
            List.sum_append, ih, hinner]
        · simp [fifthThenSixthEvents, fifthSixthWithoutBoth,
            hr, hs, List.map_append, List.sum_append, ih]
      · by_cases hs : S (!positive) (p :: pre) = true
        · simp [fifthThenSixthEvents, fifthSixthWithoutBoth,
            hr, hs, List.map_append, List.sum_append, ih]
        · simp [fifthThenSixthEvents, fifthSixthWithoutBoth,
            hr, hs, List.map_append, List.sum_append, ih]

/-- A rank-four actual frontier occurrence is positive. This is derived
from the kernel-facing original sign/parity invariant and the real
selected-prefix length, rather than inserted as a second source field. -/
private theorem evenListLength_four {α : Type*}
    (xs : List α) (hx : xs.length = 4) :
    evenListLength xs = true := by
  cases xs with
  | nil => simp at hx
  | cons a xs =>
      cases xs with
      | nil => simp at hx
      | cons b xs =>
          cases xs with
          | nil => simp at hx
          | cons c xs =>
              cases xs with
              | nil => simp at hx
              | cons d xs =>
                  cases xs with
                  | nil => simp [evenListLength]
                  | cons e ys =>
                      simp only [List.length_cons] at hx
                      omega

private theorem actual_rank_four_positive
    (e : ℚ) (q : ℕ) (om : ℝ) (N cap : ℕ) (w z : ℝ)
    (state : FirstExitDepthState ℕ)
    (hs : state ∈ sharedRankFour e q om N cap w z) :
    state.positive = true := by
  have hl : state.selectedPrefix.length = 4 :=
    firstExitDepthFrontier_selected_length 4
      (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
      (fun _ : ℕ => (1 : ℝ)) []
      (roughPrimeUniverse N cap w z) true 1 (by simp) state hs
  calc
    state.positive = evenListLength state.selectedPrefix :=
      mem_firstExitDepthFrontier_positive_eq_evenListLength 4
        (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
        (fun _ : ℕ => (1 : ℝ))
        (roughPrimeUniverse N cap w z) state hs
    _ = true := evenListLength_four state.selectedPrefix hl

/-- The real source-only event list now contains fifth-only and sixth-only
admissions; the BOTH-sixth category is absent, but all other occurrences
remain in original order, with the original suffix and full physical test. -/
def actualFifthSixthWithoutBoth
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (state : FirstExitDepthState ℕ) : List (FifthSixthStoppedEvent ℕ) :=
  fifthSixthWithoutBoth
    (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
    (P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ))
    (fun _ : ℕ => (1 : ℝ))
    (attachedLeafTest N cap 1 w L (highQTest X F))
    state.selectedPrefix state.positive state.mass state.remaining

/-- The high-q cancellation is instantiated on the literal SAME fourth
parent and SAME fifth/sixth ordered carrier. This eliminates the zero
sixth-BOTH class for both g=id and g=abs, without paying it twice. -/
theorem actual_fourth_signed_or_abs_drop_sixth_both
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ)
    (he : (0 : ℝ) ≤
      ((P4AOriginalCompleteSixthChronology.data e q om).e : ℝ))
    (hN : 1 < (N : ℝ))
    (epsilon : ℝ) (heps : epsilon ≤ (1 / 500 : ℝ))
    (X : ℕ) (hX : (N : ℝ) ^ (3 / 5 : ℝ) ≤ (X : ℝ))
    (F : ℕ → ℝ) (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w z)
    (g : ℝ → ℝ) (hg : g 0 = 0) :
    ((actualFifthSixthEvents delta n e q om N cap w
      ((N : ℝ) ^ epsilon) X F state).map
      (fun event => g event.signedValue)).sum =
    ((actualFifthSixthWithoutBoth delta n e q om N cap w
      ((N : ℝ) ^ epsilon) X F state).map
      (fun event => g event.signedValue)).sum := by
  have hl : state.selectedPrefix.length = 4 :=
    firstExitDepthFrontier_selected_length 4
      (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
      (fun _ : ℕ => (1 : ℝ)) []
      (roughPrimeUniverse N cap w z) true 1 (by simp) state hstate
  have hp : state.positive = true :=
    actual_rank_four_positive e q om N cap w z state hstate
  refine fifthThenSixth_map_sum_drop_both
    (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
    (P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ))
    (fun _ : ℕ => (1 : ℝ))
    (attachedLeafTest N cap 1 w ((N : ℝ) ^ epsilon)
      (highQTest X F))
    state.selectedPrefix state.positive state.mass state.remaining
    g hg ?_
  intro p pp tail
    have hzero :=
      actual_rank_six_stopped_difference_zero_at_highq
        delta n e q om N cap w he hN epsilon heps X hX F
        (pp :: p :: state.selectedPrefix) (by simp [hl])
        ((state.mass * (1 : ℝ)) * (1 : ℝ)) tail
    exact by
      simpa [hp] using (sub_eq_zero.mp hzero)

/-- The actual early stopped SIGNED difference now has no sixth-BOTH
invoice. The equality holds for the complete shared-rank-four occurrence
List, not a replacement source or a set of distinct parents. -/
theorem actual_stopped_difference_eq_fifth_sixth_exclusives
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ)
    (he : (0 : ℝ) ≤
      ((P4AOriginalCompleteSixthChronology.data e q om).e : ℝ))
    (hN : 1 < (N : ℝ))
    (epsilon : ℝ) (heps : epsilon ≤ (1 / 500 : ℝ))
    (X : ℕ) (hX : (N : ℝ) ^ (3 / 5 : ℝ) ≤ (X : ℝ))
    (F : ℕ → ℝ) :
    rawStopped e q om N cap w z ((N : ℝ) ^ epsilon) X F -
      licensedStopped delta n e q om N cap w z
        ((N : ℝ) ^ epsilon) X F =
    ((sharedRankFour e q om N cap w z).map (fun state =>
      ((actualFifthSixthWithoutBoth delta n e q om N cap w
        ((N : ℝ) ^ epsilon) X F state).map
          FifthSixthStoppedEvent.signedValue).sum)).sum := by
  rw [actual_stopped_difference_eq_fifth_sixth_events]
  apply congrArg List.sum
  apply List.map_congr_left
  intro state hs
  simpa using actual_fourth_signed_or_abs_drop_sixth_both
    delta n e q om N cap w z he hN epsilon heps X hX F
    state hs id (by simp)

/-- This is the replacement fifth/sixth EXCLUSIVE invoice. It charges
the actual one-sided stopped subtrees and no sixth-BOTH zero source.
No density/PP asymptotic saving is assumed for the survivors. -/
def actualFifthSixthExclusiveAbsInvoice
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) : ℝ :=
  ((sharedRankFour e q om N cap w z).map (fun state =>
    ((actualFifthSixthWithoutBoth delta n e q om N cap w L X F state).map
      (fun event => |event.signedValue|)).sum)).sum

private theorem abs_nested_sum_le {α β : Type*}
    (xs : List α) (f : α → List β) (g : β → ℝ) :
    |(xs.map (fun s => ((f s).map g).sum)).sum| ≤
      (xs.map (fun s => ((f s).map (fun e => |g e|)).sum)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hinner : |((f x).map g).sum| ≤
          ((f x).map (fun e => |g e|)).sum := by
        induction (f x) with
        | nil => simp
        | cons e es ih' =>
            simpa only [List.map_cons, List.sum_cons] using
              (abs_add (g e) ((es.map g).sum)).trans
                (add_le_add_left ih' |g e|)
      simpa only [List.map_cons, List.sum_cons] using
        (abs_add ((f x).map g).sum ((xs.map (fun s => ((f s).map g).sum)).sum)).trans
          (add_le_add hinner ih)

theorem abs_actual_stopped_le_fifth_sixth_exclusive_invoice
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ)
    (he : (0 : ℝ) ≤
      ((P4AOriginalCompleteSixthChronology.data e q om).e : ℝ))
    (hN : 1 < (N : ℝ))
    (epsilon : ℝ) (heps : epsilon ≤ (1 / 500 : ℝ))
    (X : ℕ) (hX : (N : ℝ) ^ (3 / 5 : ℝ) ≤ (X : ℝ))
    (F : ℕ → ℝ) :
    |rawStopped e q om N cap w z ((N : ℝ) ^ epsilon) X F -
      licensedStopped delta n e q om N cap w z
        ((N : ℝ) ^ epsilon) X F| ≤
    actualFifthSixthExclusiveAbsInvoice delta n e q om N cap w z
      ((N : ℝ) ^ epsilon) X F := by
  rw [actual_stopped_difference_eq_fifth_sixth_exclusives
    delta n e q om N cap w z he hN epsilon heps X hX F]
  exact abs_nested_sum_le (sharedRankFour e q om N cap w z)
    (actualFifthSixthWithoutBoth delta n e q om N cap w
      ((N : ℝ) ^ epsilon) X F)
    FifthSixthStoppedEvent.signedValue

/-- The eliminated sixth-BOTH events genuinely had zero absolute value;
this invoice is the OLD fifth/sixth invoice with its zero events removed,
not an additional charge. This is equality of bills, not a claim of
positive numerical saving from zero terms. -/
theorem reduced_invoice_eq_original_fifth_sixth_invoice
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ)
    (he : (0 : ℝ) ≤
      ((P4AOriginalCompleteSixthChronology.data e q om).e : ℝ))
    (hN : 1 < (N : ℝ))
    (epsilon : ℝ) (heps : epsilon ≤ (1 / 500 : ℝ))
    (X : ℕ) (hX : (N : ℝ) ^ (3 / 5 : ℝ) ≤ (X : ℝ))
    (F : ℕ → ℝ) :
    actualFifthSixthExclusiveAbsInvoice delta n e q om N cap w z
      ((N : ℝ) ^ epsilon) X F =
    P4AOriginalFull87FifthSixthStoppedEvents.actualFifthSixthAbsInvoice
      delta n e q om N cap w z ((N : ℝ) ^ epsilon) X F := by
  apply congrArg List.sum
  apply List.map_congr_left
  intro state hs
  exact (actual_fourth_signed_or_abs_drop_sixth_both
    delta n e q om N cap w z he hN epsilon heps X hX F
    state hs (fun t => |t|) (by simp)).symm

/-- One physical ledger inequality, charging the surviving fifth/sixth
one-sided stopped trees ONCE and the earlier five rank-eight frontier
classes ONCE. It does not set the whole difference to zero. -/
theorem abs_full_physical_le_exclusive_fifth_sixth_and_frontier
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ)
    (he : (0 : ℝ) ≤
      ((P4AOriginalCompleteSixthChronology.data e q om).e : ℝ))
    (hN : 1 < (N : ℝ))
    (epsilon : ℝ) (heps : epsilon ≤ (1 / 500 : ℝ))
    (X : ℕ) (hX : (N : ℝ) ^ (3 / 5 : ℝ) ≤ (X : ℝ))
    (F : ℕ → ℝ) :
    |P4AOriginalLicensedSixthSignedLedger.physical
        (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
        N cap w z ((N : ℝ) ^ epsilon) (highQTest X F) -
      P4AOriginalLicensedSixthSignedLedger.physical
        (P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ))
        N cap w z ((N : ℝ) ^ epsilon) (highQTest X F)| ≤
    actualFifthSixthExclusiveAbsInvoice delta n e q om N cap w z
      ((N : ℝ) ^ epsilon) X F +
      ((rawOutsideHighQInvoice delta e q om N cap w z
          ((N : ℝ) ^ epsilon) X F +
        actualProducerThreeClassLeafBill delta n e q om N cap w z
          ((N : ℝ) ^ epsilon) X F) +
        licensedOutsideHighQInvoice delta n e q om N cap w z
          ((N : ℝ) ^ epsilon) X F) := by
  exact (abs_actual_full_physical_difference_le_stop_and_five_leaf_classes
    delta n e q om N cap w z ((N : ℝ) ^ epsilon) X F).trans
    (add_le_add_right
      (abs_actual_stopped_le_fifth_sixth_exclusive_invoice
        delta n e q om N cap w z he hN epsilon heps X hX F) _)

end
end ImbalancedChen.P4AOriginalFull87SixthBothInvoice
