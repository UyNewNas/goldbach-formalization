import ImbalancedChen.P4AOriginalFull87EarlyStopPhysicalGap
import ImbalancedChen.P4AOriginalFull87LicensedSixthPolicy
import ImbalancedChen.P1Pair12RetainedSignedSource
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

The missing physical early-stopped discrepancy is NOT a depth-eight
frontier leaf cost.  The actual complete-sixth RAW and licensed-sixth
policies have the SAME admission decisions through rank four (the
existing through_four_eq_raw lemma), but may disagree at rank five
and later.  We localize their stopped-before-eight difference on the
literal shared rank-four first-exit frontier, retaining each copy,
the actual sign, mass, attached small Rosser beta, and strict full-q
terminal test.  No early stopped equality or quantitative saving is
assumed.

This is a structural candidate, NOT a numerical H_N payment.
-/

namespace ImbalancedChen.P4AOriginalFull87RankFourStoppedLocalization
noncomputable section
open scoped Classical BigOperators
open P1Pair12RetainedSignedSource (stoppedTest attachedLeafTest)
open P4AOriginalFull87EarlyStopPhysicalGap
  (rawStopped licensedStopped
   abs_actual_full_physical_difference_le_stop_and_five_leaf_classes)
open P4AOriginalFull87PhysicalHighQOwnedInvoice (highQTest)
open P4AOriginalFull87RawTrimSignedHighQ (rawOutsideHighQInvoice)
open P4AOriginalFull87LicensedOutsideThreeInvoices (licensedOutsideHighQInvoice)
open P4AOriginalFull87ThreeClassLeafInvoices (actualProducerThreeClassLeafBill)

/-- Recursive stopped conservation at two genuine depths.  A branch
exhausted before j remains in stopped(j); a branch that reaches j
contributes its *own* still-stoppable suffix through the rank-j list.
No conversion to a Finset, so repeated occurrences survive. -/
theorem stoppedTest_split_at {α : Type*} (j k : ℕ) (hjk : j ≤ k)
    (R : Bool → List α → Bool) (h : α → ℝ)
    (T : Bool → List α → ℝ) (pre remaining : List α)
    (positive : Bool) (mass : ℝ) :
    stoppedTest k R h T pre positive mass remaining =
      stoppedTest j R h T pre positive mass remaining +
        ((firstExitDepthFrontier j R h pre positive mass remaining).map
          (fun s => stoppedTest k R h T s.selectedPrefix
            s.positive s.mass s.remaining)).sum := by
  induction remaining generalizing pre positive mass with
  | nil =>
      by_cases hj : j ≤ pre.length
      · simp [stoppedTest, firstExitDepthFrontier, hj]
      · have hk : ¬ k ≤ pre.length := by omega
        simp [stoppedTest, firstExitDepthFrontier, hj, hk]
  | cons p ps ih =>
      by_cases hj : j ≤ pre.length
      · simp [stoppedTest, firstExitDepthFrontier, hj]
      · have hk : ¬ k ≤ pre.length := by omega
        simp only [stoppedTest, firstExitDepthFrontier, if_neg hj, if_neg hk]
        by_cases hr : R (!positive) (p :: pre) = true
        · simp only [if_pos hr, List.map_append, List.sum_append]
          rw [ih pre positive mass, ih (p :: pre) (!positive) (mass * h p)]
          ring
        · simp only [if_neg hr, add_zero, List.append_nil]
          exact ih pre positive mass

/-- The stopped-before-j source reads only admission decisions queried
at length <= j.  Equal early policies have exactly the same stops. -/
theorem stoppedTest_congr_through_cut {α : Type*} (j : ℕ)
    (R S : Bool → List α → Bool) (h : α → ℝ)
    (T : Bool → List α → ℝ)
    (agree : ∀ b pre, pre.length ≤ j → R b pre = S b pre)
    (pre remaining : List α) (positive : Bool) (mass : ℝ) :
    stoppedTest j R h T pre positive mass remaining =
      stoppedTest j S h T pre positive mass remaining := by
  induction remaining generalizing pre positive mass with
  | nil => rfl
  | cons p ps ih =>
      by_cases hj : j ≤ pre.length
      · simp [stoppedTest, hj]
      · have hquery : (p :: pre).length ≤ j := by omega
        have heq := agree (!positive) (p :: pre) hquery
        simp only [stoppedTest, if_neg hj]
        rw [heq, ih pre positive mass,
          ih (p :: pre) (!positive) (mass * h p)]

/-- The rank-j frontier itself also depends only on those same early
admission decisions, including sign, physical mass and remaining list. -/
theorem frontier_congr_through_cut {α : Type*} (j : ℕ)
    (R S : Bool → List α → Bool) (h : α → ℝ)
    (agree : ∀ b pre, pre.length ≤ j → R b pre = S b pre)
    (pre remaining : List α) (positive : Bool) (mass : ℝ) :
    firstExitDepthFrontier j R h pre positive mass remaining =
      firstExitDepthFrontier j S h pre positive mass remaining := by
  induction remaining generalizing pre positive mass with
  | nil => rfl
  | cons p ps ih =>
      by_cases hj : j ≤ pre.length
      · simp [firstExitDepthFrontier, hj]
      · have hquery : (p :: pre).length ≤ j := by omega
        have heq := agree (!positive) (p :: pre) hquery
        simp only [firstExitDepthFrontier, if_neg hj]
        rw [heq, ih pre positive mass,
          ih (p :: pre) (!positive) (mass * h p)]

private theorem list_sum_map_sub {α : Type*} (xs : List α) (f g : α → ℝ) :
    (xs.map f).sum - (xs.map g).sum =
      (xs.map (fun s => f s - g s)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [← ih]
      ring

private theorem abs_list_sum_le_sum_abs {α : Type*}
    (xs : List α) (f : α → ℝ) :
    |(xs.map f).sum| ≤ (xs.map (fun s => |f s|)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      exact (abs_add _ _).trans (add_le_add_left ih _)

/-- The exact SAME actual first-exit rank-four parent list for both
producers.  It uses the ORIGINAL RAW policy, not a made-up parent or
an archival surrogate. -/
def sharedRankFour (e : ℚ) (q : ℕ) (om : ℝ) (N cap : ℕ)
    (w z : ℝ) : List (FirstExitDepthState ℕ) :=
  firstExitDepthFrontier 4
    (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
    (fun _ : ℕ => (1 : ℝ)) [] true 1
    (roughPrimeUniverse N cap w z)

/-- Both genuine producers have exactly this four-decision history,
but we DO NOT identify their later fifth/sixth continuation. -/
theorem licensed_rank_four_eq_raw
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) :
    firstExitDepthFrontier 4
      (P4AOriginalFull87LicensedSixthPolicy.policy
        delta n e q om (N : ℝ))
      (fun _ : ℕ => (1 : ℝ)) [] true 1
      (roughPrimeUniverse N cap w z) =
    sharedRankFour e q om N cap w z := by
  apply (frontier_congr_through_cut 4
    (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
    (P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ))
    (fun _ : ℕ => (1 : ℝ)) (by
      intro b pre hp
      exact (P4AOriginalFull87LicensedSixthPolicy.through_four_eq_raw
        delta n e q om (N : ℝ) b pre hp).symm)
    [] (roughPrimeUniverse N cap w z) true 1).symm

/-- The exact early-stopped difference arises only *below the actual
shared fourth frontier*, hence its first possible disagreement is in
the fifth admission test. The suffix may include sixth and later
decisions and exhausted carriers; none is silently discarded. -/
theorem actual_stopped_difference_eq_shared_four_suffix
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) :
    rawStopped e q om N cap w z L X F -
      licensedStopped delta n e q om N cap w z L X F =
    ((sharedRankFour e q om N cap w z).map (fun s =>
      stoppedTest 8
        (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
        (fun _ : ℕ => (1 : ℝ))
        (attachedLeafTest N cap 1 w L (highQTest X F))
        s.selectedPrefix s.positive s.mass s.remaining -
      stoppedTest 8
        (P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ))
        (fun _ : ℕ => (1 : ℝ))
        (attachedLeafTest N cap 1 w L (highQTest X F))
        s.selectedPrefix s.positive s.mass s.remaining)).sum := by
  let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
  let S := P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ)
  let h : ℕ → ℝ := fun _ => 1
  let T := attachedLeafTest N cap 1 w L (highQTest X F)
  let carrier := roughPrimeUniverse N cap w z
  have hagree : ∀ b pre, pre.length ≤ 4 → R b pre = S b pre := by
    intro b pre hp
    exact (P4AOriginalFull87LicensedSixthPolicy.through_four_eq_raw
      delta n e q om (N : ℝ) b pre hp).symm
  have hstop := stoppedTest_congr_through_cut 4 R S h T hagree
    [] carrier true 1
  have hfront := frontier_congr_through_cut 4 R S h hagree
    [] carrier true 1
  have hR := stoppedTest_split_at 4 8 (by omega) R h T
    [] carrier true 1
  have hS := stoppedTest_split_at 4 8 (by omega) S h T
    [] carrier true 1
  change stoppedTest 8 R h T [] true 1 carrier -
      stoppedTest 8 S h T [] true 1 carrier =
    ((firstExitDepthFrontier 4 R h [] true 1 carrier).map (fun s =>
      stoppedTest 8 R h T s.selectedPrefix s.positive s.mass s.remaining -
      stoppedTest 8 S h T s.selectedPrefix s.positive s.mass s.remaining)).sum
  rw [hR, hS, ← hstop, ← hfront]
  have hsum := list_sum_map_sub
    (firstExitDepthFrontier 4 R h [] true 1 carrier)
    (fun s => stoppedTest 8 R h T s.selectedPrefix s.positive s.mass s.remaining)
    (fun s => stoppedTest 8 S h T s.selectedPrefix s.positive s.mass s.remaining)
  linarith only [hsum]

/-- A genuinely distinct EARLY-STOP invoice, indexed by rank-four
occurrence rather than by rank-eight leaves. The absolute value is
inside this sum; no cancellation is presumed between different
original fourth-parent histories. -/
def sharedRankFourStoppedInvoice
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) : ℝ :=
  ((sharedRankFour e q om N cap w z).map (fun s =>
    |stoppedTest 8
      (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
      (fun _ : ℕ => (1 : ℝ))
      (attachedLeafTest N cap 1 w L (highQTest X F))
      s.selectedPrefix s.positive s.mass s.remaining -
    stoppedTest 8
      (P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ))
      (fun _ : ℕ => (1 : ℝ))
      (attachedLeafTest N cap 1 w L (highQTest X F))
      s.selectedPrefix s.positive s.mass s.remaining|)).sum

theorem abs_actual_early_stops_le_shared_four_invoice
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) :
    |rawStopped e q om N cap w z L X F -
      licensedStopped delta n e q om N cap w z L X F| ≤
    sharedRankFourStoppedInvoice delta n e q om N cap w z L X F := by
  rw [actual_stopped_difference_eq_shared_four_suffix]
  exact abs_list_sum_le_sum_abs _ _

/-- Complete physical rho: rank-four early-stop invoice exactly ONCE,
then the previous five separate rank-eight source invoices.  Still
UNPAID relative to H_N; the older frontier-only estimate is retained. -/
theorem abs_full_physical_le_four_stops_and_five_frontier_classes
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) :
    |P4AOriginalLicensedSixthSignedLedger.physical
        (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
        N cap w z L (highQTest X F) -
      P4AOriginalLicensedSixthSignedLedger.physical
        (P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ))
        N cap w z L (highQTest X F)| ≤
      sharedRankFourStoppedInvoice delta n e q om N cap w z L X F +
      ((rawOutsideHighQInvoice delta e q om N cap w z L X F +
        actualProducerThreeClassLeafBill delta n e q om N cap w z L X F) +
        licensedOutsideHighQInvoice delta n e q om N cap w z L X F) := by
  exact (abs_actual_full_physical_difference_le_stop_and_five_leaf_classes
    delta n e q om N cap w z L X F).trans
    (add_le_add_right
      (abs_actual_early_stops_le_shared_four_invoice
        delta n e q om N cap w z L X F) _)

end
end ImbalancedChen.P4AOriginalFull87RankFourStoppedLocalization
