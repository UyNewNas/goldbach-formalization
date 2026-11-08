import ImbalancedChen.P4AOriginalFull87RankFourStoppedLocalization
import ImbalancedChen.P4AOriginalFull87EarlyStopPhysicalGap
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

The two REAL complete-sixth and licensed-sixth policies have the identical
rank-four first-exit frontier, but their next (rank-five) admission decisions
may differ. This packet tracks each possible fifth selected prime IN ORDER,
with its genuine suffix carrier, sign and mass, and splits the stopped-before-
eight difference into raw-only, both-admitted and licensed-only cases.

IMPORTANT: At a potential fifth prime p, recursion uses the tail AFTER p,
not the whole original rough-prime carrier. A list map on p alone would be
wrong. Events are computed recursively on the genuine remaining List.

The both-admitted event still contains the actual sixth/seventh stopped
difference. Neither it nor the exclusive events are assumed small or zero.
No arbitrary witness, archive coefficient, assumption, PP theorem or reserve
is inserted.
-/

namespace ImbalancedChen.P4AOriginalFull87FirstFifthStoppedEvents
noncomputable section
open scoped Classical BigOperators
open P1Pair12RetainedSignedSource (stoppedTest attachedLeafTest)
open P4AOriginalFull87RankFourStoppedLocalization
  (sharedRankFour actual_stopped_difference_eq_shared_four_suffix)
open P4AOriginalFull87EarlyStopPhysicalGap
  (rawStopped licensedStopped
   abs_actual_full_physical_difference_le_stop_and_five_leaf_classes)
open P4AOriginalFull87PhysicalHighQOwnedInvoice (highQTest)
open P4AOriginalFull87RawTrimSignedHighQ (rawOutsideHighQInvoice)
open P4AOriginalFull87LicensedOutsideThreeInvoices (licensedOutsideHighQInvoice)
open P4AOriginalFull87ThreeClassLeafInvoices (actualProducerThreeClassLeafBill)

inductive FifthAdmissionClass where
  | rawOnly
  | both
  | licensedOnly
  deriving DecidableEq, Repr

/-- Computed event for one actual fifth-admission query. The complete
post-query carrier and incoming physical prefix/sign/mass are retained.
signedValue is calculated below from the original stoppedTest, not supplied
as an independent certificate. -/
structure FifthStoppedEvent (α : Type*) where
  selectedAfter : List α
  positiveAfter : Bool
  massAfter : ℝ
  remainingAfter : List α
  kind : FifthAdmissionClass
  signedValue : ℝ

/-- One-copy recursive traversal of all eligible fifth queries from a
FIXED fourth prefix. The skipped prime is never added to that prefix.
For an admitted child the actual remaining tail, not the whole carrier,
is used in stoppedTest 8. Every occurrence (including repeated p) is kept. -/
def firstFifthEvents {α : Type*}
    (R S : Bool → List α → Bool) (h : α → ℝ)
    (T : Bool → List α → ℝ)
    (pre : List α) (positive : Bool) (mass : ℝ) :
    List α → List (FifthStoppedEvent α)
  | [] => []
  | p :: ps =>
      let r := stoppedTest 8 R h T (p :: pre) (!positive) (mass * h p) ps
      let s := stoppedTest 8 S h T (p :: pre) (!positive) (mass * h p) ps
      let emit (kind : FifthAdmissionClass) (value : ℝ) :
          List (FifthStoppedEvent α) :=
        [⟨p :: pre, !positive, mass * h p, ps, kind, value⟩]
      let now :=
        if R (!positive) (p :: pre) = true then
          if S (!positive) (p :: pre) = true then
            emit .both (r - s)
          else emit .rawOnly r
        else if S (!positive) (p :: pre) = true then
          emit .licensedOnly (-s)
        else []
      now ++ firstFifthEvents R S h T pre positive mass ps

/-- Exact FIRST FIFTH classification, retaining signed differences in
the both-admitted case. The only assumption is that the incoming prefix
has not already hit depth eight; actual application is at length four.
No post-fifth equality or cap monotonicity is used. -/
theorem stopped_difference_eq_first_fifth_events {α : Type*}
    (R S : Bool → List α → Bool) (h : α → ℝ)
    (T : Bool → List α → ℝ)
    (pre : List α) (positive : Bool) (mass : ℝ)
    (remaining : List α) (hpre : pre.length < 8) :
    stoppedTest 8 R h T pre positive mass remaining -
      stoppedTest 8 S h T pre positive mass remaining =
    ((firstFifthEvents R S h T pre positive mass remaining).map
      (fun event => event.signedValue)).sum := by
  induction remaining with
  | nil =>
      have hk : ¬ 8 ≤ pre.length := by omega
      simp [stoppedTest, firstFifthEvents, hk]
  | cons p ps ih =>
      have hk : ¬ 8 ≤ pre.length := by omega
      cases hr : R (!positive) (p :: pre) <;>
        cases hs : S (!positive) (p :: pre) <;>
        simp [stoppedTest, firstFifthEvents, hk, hr, hs,
          List.map_append, List.sum_append] <;>
        linear_combination ih

private theorem abs_map_sum_le {α : Type*}
    (xs : List α) (f : α → ℝ) :
    |(xs.map f).sum| ≤ (xs.map (fun x => |f x|)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      exact (abs_add _ _).trans (add_le_add_left ih _)

private theorem abs_nested_map_sum_le {α β : Type*}
    (xs : List α) (g : α → List β) (f : β → ℝ) :
    |(xs.map (fun x => ((g x).map f).sum)).sum| ≤
      (xs.map (fun x => ((g x).map (fun t => |f t|)).sum)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      exact (abs_add _ _).trans (add_le_add (abs_map_sum_le (g x) f) ih)

/-- Actual raw rank-five gate, not an action from a frozen numerical cell. -/
theorem raw_fifth_gate
    (e : ℚ) (q : ℕ) (om N : ℝ)
    (pre : List ℕ) (p : ℕ) (positive : Bool)
    (hpre : pre.length = 4) :
    P4AOriginalFull87CompleteSixthDispatch.policy e q om N
        (!positive) (p :: pre) =
      P4AOriginalCompleteSixthChronology.currentSixthPolicy e q om N
        (!positive) (p :: pre) := by
  exact P4AOriginalFull87CompleteSixthDispatch.policy_through_eight
    e q om N (!positive) (p :: pre) (by simp [hpre])

/-- Actual licensed rank-five gate is STILL its finite fifth predecessor.
The sixth splice cannot alter a length-five query. -/
theorem licensed_fifth_gate
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ)
    (pre : List ℕ) (p : ℕ) (positive : Bool)
    (hpre : pre.length = 4) :
    P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om N
        (!positive) (p :: pre) =
      P4AOriginalFull87FiniteParentPolicy.fifthPolicy n e q om N
        (!positive) (p :: pre) := by
  have h8 : (p :: pre).length ≤ 8 := by simp [hpre]
  have h6 : (p :: pre).length ≤ 6 := by simp [hpre]
  rw [P4AOriginalFull87LicensedSixthPolicy.through_eight
    delta n e q om N (!positive) (p :: pre) h8]
  simp only [P4AOriginalFull87LicensedSixthPolicy.sixthPolicy,
    firstExitDepthSplicePolicy, if_pos h6]

/-- Original actual policies and the original signed full-modulus terminal
are passed directly, so every emitted branch is a genuine fifth gate on
the true shared fourth history, with actual strict X < full q. -/
def actualFifthEvents
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (state : FirstExitDepthState ℕ) : List (FifthStoppedEvent ℕ) :=
  firstFifthEvents
    (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
    (P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ))
    (fun _ : ℕ => (1 : ℝ))
    (attachedLeafTest N cap 1 w L (highQTest X F))
    state.selectedPrefix state.positive state.mass state.remaining

/-- A source member has EXACTLY four selected primes, with multiplicity
and the genuine incoming mass retained. -/
theorem actual_fourth_state_first_fifth_decomposition
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w z) :
    stoppedTest 8
        (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
        (fun _ : ℕ => (1 : ℝ))
        (attachedLeafTest N cap 1 w L (highQTest X F))
        state.selectedPrefix state.positive state.mass state.remaining -
      stoppedTest 8
        (P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ))
        (fun _ : ℕ => (1 : ℝ))
        (attachedLeafTest N cap 1 w L (highQTest X F))
        state.selectedPrefix state.positive state.mass state.remaining =
      ((actualFifthEvents delta n e q om N cap w L X F state).map
        (fun event => event.signedValue)).sum := by
  have hlen : state.selectedPrefix.length = 4 := by
    exact firstExitDepthFrontier_selected_length 4
      (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
      (fun _ : ℕ => (1 : ℝ)) []
      (roughPrimeUniverse N cap w z) true 1 (by simp) state hstate
  exact stopped_difference_eq_first_fifth_events
    (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
    (P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ))
    (fun _ : ℕ => (1 : ℝ))
    (attachedLeafTest N cap 1 w L (highQTest X F))
    state.selectedPrefix state.positive state.mass state.remaining (by omega)

/-- Unlike a re-labelled absolute early-stop total, this is an exact
SIGNED decomposition into concrete fifth-gate events for EACH original
fourth history and its genuine suffix. -/
theorem actual_stopped_difference_eq_first_fifth_events
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) :
    rawStopped e q om N cap w z L X F -
      licensedStopped delta n e q om N cap w z L X F =
    ((sharedRankFour e q om N cap w z).map (fun state =>
      ((actualFifthEvents delta n e q om N cap w L X F state).map
        (fun event => event.signedValue)).sum)).sum := by
  rw [actual_stopped_difference_eq_shared_four_suffix]
  apply congrArg List.sum
  apply List.map_congr_left
  intro state hstate
  exact actual_fourth_state_first_fifth_decomposition
    delta n e q om N cap w z L X F state hstate

/-- A distinct per-occurrence unsigned payment. Its three event classes
include raw-only, both-admitted and licensed-only. The both-admitted fee
can contain sixth/seventh stopped differences; NOTHING here bounds it
as o(H_N). -/
def actualFirstFifthAbsInvoice
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) : ℝ :=
  ((sharedRankFour e q om N cap w z).map (fun state =>
    ((actualFifthEvents delta n e q om N cap w L X F state).map
      (fun event => |event.signedValue|)).sum)).sum

theorem abs_stopped_difference_le_first_fifth_invoice
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) :
    |rawStopped e q om N cap w z L X F -
      licensedStopped delta n e q om N cap w z L X F| ≤
    actualFirstFifthAbsInvoice delta n e q om N cap w z L X F := by
  rw [actual_stopped_difference_eq_first_fifth_events]
  exact abs_nested_map_sum_le (sharedRankFour e q om N cap w z)
    (actualFifthEvents delta n e q om N cap w L X F)
    (fun event => event.signedValue)

/-- Full physical discrepancy: the NEW rank-five event bill exactly
replaces the earlier rank-four stopped invoice. All five separate
rank-eight frontier invoices are kept once, NEVER paid twice. -/
theorem abs_full_physical_le_first_fifth_and_five_frontier_classes
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) :
    |P4AOriginalLicensedSixthSignedLedger.physical
        (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
        N cap w z L (highQTest X F) -
      P4AOriginalLicensedSixthSignedLedger.physical
        (P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ))
        N cap w z L (highQTest X F)| ≤
      actualFirstFifthAbsInvoice delta n e q om N cap w z L X F +
      ((rawOutsideHighQInvoice delta e q om N cap w z L X F +
        actualProducerThreeClassLeafBill delta n e q om N cap w z L X F) +
        licensedOutsideHighQInvoice delta n e q om N cap w z L X F) := by
  exact (abs_actual_full_physical_difference_le_stop_and_five_leaf_classes
    delta n e q om N cap w z L X F).trans
    (add_le_add_right
      (abs_stopped_difference_le_first_fifth_invoice
        delta n e q om N cap w z L X F) _)

end
end ImbalancedChen.P4AOriginalFull87FirstFifthStoppedEvents

