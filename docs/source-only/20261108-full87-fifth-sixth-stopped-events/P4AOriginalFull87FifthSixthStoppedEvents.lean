import ImbalancedChen.P4AOriginalFull87FirstFifthStoppedEvents
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

Continuation of the actual shared-rank-four early-stop ledger.  A genuinely
BOTH-admitted fifth candidate is expanded at the actual sixth admission
gate, using the exact post-fifth tail and the ORIGINAL stoppedTest 8 on
each sixth child.  Fifth-exclusive events remain at fifth rank and are
not passed through a sixth guard.  The resulting List therefore carries
two DIFFERENT event depths with no duplicate physical charge.

This is a signed FINITE identity and its unsigned invoice, not a
same-rho/H_N asymptotic payment, saved87 replay, or Lean kernel check.
-/

namespace ImbalancedChen.P4AOriginalFull87FifthSixthStoppedEvents
noncomputable section
open scoped Classical BigOperators
open P1Pair12RetainedSignedSource (stoppedTest attachedLeafTest)
open P4AOriginalFull87FirstFifthStoppedEvents
  (FifthStoppedEvent FifthAdmissionClass firstFifthEvents
   stopped_difference_eq_first_fifth_events)
open P4AOriginalFull87RankFourStoppedLocalization
  (sharedRankFour actual_stopped_difference_eq_shared_four_suffix)
open P4AOriginalFull87EarlyStopPhysicalGap
  (rawStopped licensedStopped
   abs_actual_full_physical_difference_le_stop_and_five_leaf_classes)
open P4AOriginalFull87PhysicalHighQOwnedInvoice (highQTest)
open P4AOriginalFull87RawTrimSignedHighQ (rawOutsideHighQInvoice)
open P4AOriginalFull87LicensedOutsideThreeInvoices (licensedOutsideHighQInvoice)
open P4AOriginalFull87ThreeClassLeafInvoices (actualProducerThreeClassLeafBill)

/-- Every first-gate exclusive has one fifth-ranked payload.  Every
both-admitted fifth child instead emits the actual sixth-ranked events,
with the fifth selected prefix retained as their common history. -/
inductive FifthSixthStoppedEvent (α : Type*) where
  | fifthExclusive (event : FifthStoppedEvent α)
  | sixthFromBoth (fifthSelected : List α) (event : FifthStoppedEvent α)

/-- Neither constructor invents a source value: both use the signed
value already evaluated from the actual stopped recursion. -/
def FifthSixthStoppedEvent.signedValue {α : Type*} :
    FifthSixthStoppedEvent α → ℝ
  | .fifthExclusive e => e.signedValue
  | .sixthFromBoth _ e => e.signedValue

/-- Two successive REAL gates.  At a fifth candidate p:
  * one-sided admissions keep their signed stopped subtree once;
  * a both-admitted child is expanded at its literal sixth carrier.
The latter is exactly the firstFifthEvents recursion, now with prefix
length FIVE; hence its next query has length SIX.  No arbitrary
post-eight mask or archived geometric cell is introduced. -/
def fifthThenSixthEvents {α : Type*}
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
            (firstFifthEvents R S h T child sign childMass ps).map
              (FifthSixthStoppedEvent.sixthFromBoth child)
          else emit .rawOnly rawChild
        else if S sign child = true then
          emit .licensedOnly (-licChild)
        else []
      now ++ fifthThenSixthEvents R S h T pre positive mass ps

/-- TWO actual admission gates replace one opaque both-admitted
stopped difference.  The induction is over the literal carrier, not
a set of candidate primes: all occurrence multiplicities survive.
The both-admitted case uses the ALREADY EXISTING recursive theorem
at prefix length five, instead of assuming its sixth stops cancel. -/
theorem stopped_difference_eq_fifth_then_sixth {α : Type*}
    (R S : Bool → List α → Bool) (h : α → ℝ)
    (T : Bool → List α → ℝ)
    (pre : List α) (positive : Bool) (mass : ℝ)
    (remaining : List α) (hpre : pre.length = 4) :
    stoppedTest 8 R h T pre positive mass remaining -
      stoppedTest 8 S h T pre positive mass remaining =
    ((fifthThenSixthEvents R S h T pre positive mass remaining).map
      FifthSixthStoppedEvent.signedValue).sum := by
  induction remaining with
  | nil =>
      have hk : ¬ 8 ≤ pre.length := by omega
      simp [stoppedTest, fifthThenSixthEvents, hk]
  | cons p ps ih =>
      have hk : ¬ 8 ≤ pre.length := by omega
      have hchild :
          stoppedTest 8 R h T (p :: pre) (!positive) (mass * h p) ps -
          stoppedTest 8 S h T (p :: pre) (!positive) (mass * h p) ps =
          ((firstFifthEvents R S h T (p :: pre) (!positive)
              (mass * h p) ps).map (fun e => e.signedValue)).sum :=
        stopped_difference_eq_first_fifth_events R S h T
          (p :: pre) (!positive) (mass * h p) ps (by simp [hpre])
      cases hr : R (!positive) (p :: pre) <;>
        cases hs : S (!positive) (p :: pre) <;>
        simp [stoppedTest, fifthThenSixthEvents,
          FifthSixthStoppedEvent.signedValue, hk, hr, hs,
          List.map_append, List.map_map, List.sum_append] <;>
        linarith only [ih, hchild]

/-- At the true sixth query (prefix length six), RAW still uses the
original complete-sixth current policy, not the licensed fifth policy. -/
theorem actual_raw_sixth_gate
    (e : ℚ) (q : ℕ) (om N : ℝ)
    (pre : List ℕ) (p : ℕ) (positive : Bool)
    (hpre : pre.length = 5) :
    P4AOriginalFull87CompleteSixthDispatch.policy e q om N
      (!positive) (p :: pre) =
    P4AOriginalCompleteSixthChronology.currentSixthPolicy e q om N
      (!positive) (p :: pre) := by
  exact P4AOriginalFull87CompleteSixthDispatch.policy_through_eight
    e q om N (!positive) (p :: pre) (by simp [hpre])

/-- The true licensed sixth query is the finite predecessor gate:
the next replacement is spliced strictly AFTER the sixth admission. -/
theorem actual_licensed_sixth_gate
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ)
    (pre : List ℕ) (p : ℕ) (positive : Bool)
    (hpre : pre.length = 5) :
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

/-- Instantiation uses the EXACT same rank-four parent state and its
existing suffix; no new state or ownership hypothesis is postulated. -/
def actualFifthSixthEvents
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (state : FirstExitDepthState ℕ) : List (FifthSixthStoppedEvent ℕ) :=
  fifthThenSixthEvents
    (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
    (P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ))
    (fun _ : ℕ => (1 : ℝ))
    (attachedLeafTest N cap 1 w L (highQTest X F))
    state.selectedPrefix state.positive state.mass state.remaining

/-- One real fourth-state occurrence. Sixth-ranked events are created
ONLY under the both-admitted fifth case, with that child's exact
remaining suffix, and remain stopped-before-eight (rank seven may
still exhaust its carrier). -/
theorem actual_fourth_state_two_gate_decomposition
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
      ((actualFifthSixthEvents delta n e q om N cap w L X F state).map
        FifthSixthStoppedEvent.signedValue).sum := by
  have hlen : state.selectedPrefix.length = 4 :=
    firstExitDepthFrontier_selected_length 4
      (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
      (fun _ : ℕ => (1 : ℝ)) []
      (roughPrimeUniverse N cap w z) true 1 (by simp) state hstate
  exact stopped_difference_eq_fifth_then_sixth
    (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
    (P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ))
    (fun _ : ℕ => (1 : ℝ))
    (attachedLeafTest N cap 1 w L (highQTest X F))
    state.selectedPrefix state.positive state.mass state.remaining hlen

/-- Global exact stopped delta, reusing the source parent and EVERY
rank-four List occurrence. In particular, the sixth events here
cannot be added as a second bill on top of the old both-admitted fee. -/
theorem actual_stopped_difference_eq_fifth_sixth_events
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) :
    rawStopped e q om N cap w z L X F -
      licensedStopped delta n e q om N cap w z L X F =
    ((sharedRankFour e q om N cap w z).map (fun state =>
      ((actualFifthSixthEvents delta n e q om N cap w L X F state).map
        FifthSixthStoppedEvent.signedValue).sum)).sum := by
  rw [actual_stopped_difference_eq_shared_four_suffix]
  apply congrArg List.sum
  apply List.map_congr_left
  intro state hstate
  exact actual_fourth_state_two_gate_decomposition
    delta n e q om N cap w z L X F state hstate

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

/-- This bill pays fifth-exclusive events and actual sixth-ranked
events after BOTH-admitted fifth decisions, ONCE. There is no
quantitative bound against H_N and no old fifth invoice is added. -/
def actualFifthSixthAbsInvoice
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) : ℝ :=
  ((sharedRankFour e q om N cap w z).map (fun state =>
    ((actualFifthSixthEvents delta n e q om N cap w L X F state).map
      (fun event => |event.signedValue|)).sum)).sum

theorem abs_stopped_difference_le_fifth_sixth_invoice
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) :
    |rawStopped e q om N cap w z L X F -
      licensedStopped delta n e q om N cap w z L X F| ≤
    actualFifthSixthAbsInvoice delta n e q om N cap w z L X F := by
  rw [actual_stopped_difference_eq_fifth_sixth_events]
  exact abs_nested_map_sum_le (sharedRankFour e q om N cap w z)
    (actualFifthSixthEvents delta n e q om N cap w L X F)
    FifthSixthStoppedEvent.signedValue

/-- True physical delta: replace the fifth-event stopped bill by the
new fifth/sixth invoice; keep prior five rank-eight categories once.
The unopened analytic same-rho_N/H_N cost is NOT smuggled in. -/
theorem abs_full_physical_le_fifth_sixth_and_five_frontier_classes
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) :
    |P4AOriginalLicensedSixthSignedLedger.physical
        (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
        N cap w z L (highQTest X F) -
      P4AOriginalLicensedSixthSignedLedger.physical
        (P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ))
        N cap w z L (highQTest X F)| ≤
      actualFifthSixthAbsInvoice delta n e q om N cap w z L X F +
      ((rawOutsideHighQInvoice delta e q om N cap w z L X F +
        actualProducerThreeClassLeafBill delta n e q om N cap w z L X F) +
        licensedOutsideHighQInvoice delta n e q om N cap w z L X F) := by
  exact (abs_actual_full_physical_difference_le_stop_and_five_leaf_classes
    delta n e q om N cap w z L X F).trans
    (add_le_add_right
      (abs_stopped_difference_le_fifth_sixth_invoice
        delta n e q om N cap w z L X F) _)

end
end ImbalancedChen.P4AOriginalFull87FifthSixthStoppedEvents
