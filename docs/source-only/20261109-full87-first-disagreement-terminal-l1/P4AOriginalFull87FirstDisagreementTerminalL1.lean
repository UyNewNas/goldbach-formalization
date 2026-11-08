import ImbalancedChen.P4AOriginalFull87StoppedTerminalPopulation
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

The actual first-disagreement full-q absolute invoice for the two independently
admitting fifth/sixth producers. Paying |rawStopped| + |licensedStopped|
would double-pay the common prefix and its unchanged exhausted histories.

At the true shared-four occurrence, skip retains the original tail;
BOTH admission recurses on the exact post-candidate tail. Only a one-sided
admission pays its OWN original stopped-terminal population. Each term keeps
the sign-selected small Rosser beta and strict X < a * selected.prod.
No H_N estimate, numerical archive certification, or reserve is supplied.
-/

namespace ImbalancedChen.P4AOriginalFull87FirstDisagreementTerminalL1
noncomputable section
open scoped Classical BigOperators
open P1Pair12RetainedSignedSource (stoppedTest attachedLeafTest)
open P4AOriginalFull87PhysicalHighQOwnedInvoice (highQTest)
open P4AOriginalFull87StoppedTerminalPopulation
  (StoppedTerminal stoppedTerminals stoppedPhysicalTerm
   actual_stopped_eq_physical_terminal_sum)
open P4AOriginalFull87RankFourStoppedLocalization
  (sharedRankFour actual_stopped_difference_eq_shared_four_suffix)
open P4AOriginalFull87EarlyStopPhysicalGap
  (rawStopped licensedStopped
   abs_actual_full_physical_difference_le_stop_and_five_leaf_classes)
open P4AOriginalFull87RawTrimSignedHighQ (rawOutsideHighQInvoice)
open P4AOriginalFull87LicensedOutsideThreeInvoices (licensedOutsideHighQInvoice)
open P4AOriginalFull87ThreeClassLeafInvoices (actualProducerThreeClassLeafBill)

/-- One original stopped terminal's actual full-modulus absolute cost. -/
def terminalFullQCharge
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (t : StoppedTerminal ℕ) : ℝ :=
  |signedTreeCoefficient t.positive t.mass| *
    ∑ a ∈ actualSmallRosserSupport N cap w,
      |if t.positive then actualSmallRosserPlus N cap w L a
       else actualSmallRosserMinus N cap w L a| *
        (if X < a * t.selected.prod then
           |F (a * t.selected.prod)| else 0)

theorem abs_stopped_physical_term_le_fullq_charge
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (t : StoppedTerminal ℕ) :
    |stoppedPhysicalTerm N cap w L X F t| ≤
      terminalFullQCharge N cap w L X F t := by
  unfold stoppedPhysicalTerm terminalFullQCharge attachedLeafTest
  rw [abs_mul]
  apply mul_le_mul_of_nonneg_left ?_
    (abs_nonneg (signedTreeCoefficient t.positive t.mass))
  calc
    |∑ a ∈ actualSmallRosserSupport N cap w,
        (if t.positive then actualSmallRosserPlus N cap w L a
         else actualSmallRosserMinus N cap w L a) *
          highQTest X F (a * t.selected.prod)| ≤
      ∑ a ∈ actualSmallRosserSupport N cap w,
        |(if t.positive then actualSmallRosserPlus N cap w L a
          else actualSmallRosserMinus N cap w L a) *
            highQTest X F (a * t.selected.prod)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ a ∈ actualSmallRosserSupport N cap w,
          |if t.positive then actualSmallRosserPlus N cap w L a
           else actualSmallRosserMinus N cap w L a| *
            (if X < a * t.selected.prod then
              |F (a * t.selected.prod)| else 0) := by
      apply Finset.sum_congr rfl
      intro a ha
      by_cases hcut : X < a * t.selected.prod
      · simp [highQTest, hcut, abs_mul]
      · simp [highQTest, hcut]

private theorem abs_map_sum_le_charge {α : Type*}
    (xs : List α) (f charge : α → ℝ)
    (h : ∀ x ∈ xs, |f x| ≤ charge x) :
    |(xs.map f).sum| ≤ (xs.map charge).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx := h x (by simp)
      have ht : ∀ y ∈ xs, |f y| ≤ charge y := by
        intro y hy
        exact h y (by simp [hy])
      simp only [List.map_cons, List.sum_cons]
      exact (abs_add _ _).trans (add_le_add hx (ih ht))

/-- Each original occurrence is charged once with its own sign and beta. -/
def stoppedTerminalL1
    (R : Bool → List ℕ → Bool) (h : ℕ → ℝ)
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (pre : List ℕ) (positive : Bool) (mass : ℝ)
    (remaining : List ℕ) : ℝ :=
  ((stoppedTerminals 8 R h pre positive mass remaining).map
    (terminalFullQCharge N cap w L X F)).sum

theorem abs_stopped_test_le_terminal_l1
    (R : Bool → List ℕ → Bool) (h : ℕ → ℝ)
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (pre : List ℕ) (positive : Bool) (mass : ℝ)
    (remaining : List ℕ) :
    |stoppedTest 8 R h
      (attachedLeafTest N cap 1 w L (highQTest X F))
      pre positive mass remaining| ≤
    stoppedTerminalL1 R h N cap w L X F
      pre positive mass remaining := by
  rw [actual_stopped_eq_physical_terminal_sum]
  unfold stoppedTerminalL1
  exact abs_map_sum_le_charge _ _ _
    (fun t _ => abs_stopped_physical_term_le_fullq_charge
      N cap w L X F t)

/-- Literal post-candidate suffix and original policy on each exclusive.
BOTH recurses and never pays either common child as a separate cost. -/
def pairEarlyStopTerminalL1
    (R S : Bool → List ℕ → Bool) (h : ℕ → ℝ)
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (pre : List ℕ) (positive : Bool) (mass : ℝ) :
    List ℕ → ℝ
  | [] => 0
  | p :: ps =>
      if 8 ≤ pre.length then 0 else
        pairEarlyStopTerminalL1 R S h N cap w L X F
          pre positive mass ps +
        (if R (!positive) (p :: pre) then
           if S (!positive) (p :: pre) then
             pairEarlyStopTerminalL1 R S h N cap w L X F
               (p :: pre) (!positive) (mass * h p) ps
           else
             stoppedTerminalL1 R h N cap w L X F
               (p :: pre) (!positive) (mass * h p) ps
         else if S (!positive) (p :: pre) then
           stoppedTerminalL1 S h N cap w L X F
             (p :: pre) (!positive) (mass * h p) ps
         else 0)

private theorem abs_pair_plus_sub_pair_le
    (a b c d A B : ℝ)
    (ha : |a - b| ≤ A) (hc : |c - d| ≤ B) :
    |(a + c) - (b + d)| ≤ A + B := by
  calc
    |(a + c) - (b + d)| = |(a - b) + (c - d)| := by
      congr 1
      ring
    _ ≤ |a - b| + |c - d| := abs_add _ _
    _ ≤ A + B := add_le_add ha hc

private theorem abs_plus_sub_base_le
    (a b c A C : ℝ)
    (ha : |a - b| ≤ A) (hc : |c| ≤ C) :
    |(a + c) - b| ≤ A + C := by
  calc
    |(a + c) - b| = |(a - b) + c| := by
      congr 1
      ring
    _ ≤ |a - b| + |c| := abs_add _ _
    _ ≤ A + C := add_le_add ha hc

private theorem abs_base_sub_plus_le
    (a b d A D : ℝ)
    (ha : |a - b| ≤ A) (hd : |d| ≤ D) :
    |a - (b + d)| ≤ A + D := by
  calc
    |a - (b + d)| = |(a - b) + (-d)| := by
      congr 1
      ring
    _ ≤ |a - b| + |-d| := abs_add _ _
    _ = |a - b| + |d| := by simp
    _ ≤ A + D := add_le_add ha hd

/-- Only first one-sided fifth/sixth/seventh gates receive terminal L1
payments; common early-stop histories cancel before any absolute value. -/
theorem abs_pair_stopped_difference_le_first_disagreement_l1
    (R S : Bool → List ℕ → Bool) (h : ℕ → ℝ)
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (pre : List ℕ) (positive : Bool) (mass : ℝ)
    (remaining : List ℕ) :
    |stoppedTest 8 R h
        (attachedLeafTest N cap 1 w L (highQTest X F))
        pre positive mass remaining -
      stoppedTest 8 S h
        (attachedLeafTest N cap 1 w L (highQTest X F))
        pre positive mass remaining| ≤
      pairEarlyStopTerminalL1 R S h N cap w L X F
        pre positive mass remaining := by
  induction remaining generalizing pre positive mass with
  | nil =>
      by_cases hk : 8 ≤ pre.length <;>
        simp [stoppedTest, pairEarlyStopTerminalL1, hk]
  | cons p ps ih =>
      by_cases hk : 8 ≤ pre.length
      · simp [stoppedTest, pairEarlyStopTerminalL1, hk]
      · let T := attachedLeafTest N cap 1 w L (highQTest X F)
        let a := stoppedTest 8 R h T pre positive mass ps
        let b := stoppedTest 8 S h T pre positive mass ps
        let c := stoppedTest 8 R h T
          (p :: pre) (!positive) (mass * h p) ps
        let d := stoppedTest 8 S h T
          (p :: pre) (!positive) (mass * h p) ps
        let A := pairEarlyStopTerminalL1 R S h N cap w L X F
          pre positive mass ps
        let B := pairEarlyStopTerminalL1 R S h N cap w L X F
          (p :: pre) (!positive) (mass * h p) ps
        let C := stoppedTerminalL1 R h N cap w L X F
          (p :: pre) (!positive) (mass * h p) ps
        let D := stoppedTerminalL1 S h N cap w L X F
          (p :: pre) (!positive) (mass * h p) ps
        have hskip : |a - b| ≤ A := ih pre positive mass
        have hboth : |c - d| ≤ B :=
          ih (p :: pre) (!positive) (mass * h p)
        have hrbound : |c| ≤ C :=
          abs_stopped_test_le_terminal_l1 R h N cap w L X F
            (p :: pre) (!positive) (mass * h p) ps
        have hsbound : |d| ≤ D :=
          abs_stopped_test_le_terminal_l1 S h N cap w L X F
            (p :: pre) (!positive) (mass * h p) ps
        cases hr : R (!positive) (p :: pre)
        · cases hs : S (!positive) (p :: pre)
          · simpa [a, b, A, T, stoppedTest,
              pairEarlyStopTerminalL1, hk, hr, hs] using hskip
          · have hcase := abs_base_sub_plus_le a b d A D hskip hsbound
            simpa [a, b, d, A, D, T, stoppedTest,
              pairEarlyStopTerminalL1, hk, hr, hs] using hcase
        · cases hs : S (!positive) (p :: pre)
          · have hcase := abs_plus_sub_base_le a b c A C hskip hrbound
            simpa [a, b, c, A, C, T, stoppedTest,
              pairEarlyStopTerminalL1, hk, hr, hs] using hcase
          · have hcase := abs_pair_plus_sub_pair_le
              a b c d A B hskip hboth
            simpa [a, b, c, d, A, B, T, stoppedTest,
              pairEarlyStopTerminalL1, hk, hr, hs] using hcase

/-- Same real rank-four source List, true raw/actual licensed gates,
and every original occurrence in the suffix. -/
def actualFirstDisagreementTerminalL1
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) : ℝ :=
  ((sharedRankFour e q om N cap w z).map (fun state =>
    pairEarlyStopTerminalL1
      (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
      (P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ))
      (fun _ : ℕ => (1 : ℝ)) N cap w L X F
      state.selectedPrefix state.positive state.mass state.remaining)).sum

theorem abs_actual_stopped_difference_le_first_disagreement_terminal_l1
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) :
    |rawStopped e q om N cap w z L X F -
      licensedStopped delta n e q om N cap w z L X F| ≤
      actualFirstDisagreementTerminalL1 delta n e q om N cap w z L X F := by
  rw [actual_stopped_difference_eq_shared_four_suffix]
  unfold actualFirstDisagreementTerminalL1
  apply abs_map_sum_le_charge
  intro state hstate
  exact abs_pair_stopped_difference_le_first_disagreement_l1
    (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
    (P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ))
    (fun _ : ℕ => (1 : ℝ)) N cap w L X F
    state.selectedPrefix state.positive state.mass state.remaining

/-- Replace the old early-stop cost, keeping the already-existing five
eighth-frontier invoices exactly ONCE; still no same-H_N payment. -/
theorem abs_full_physical_difference_le_first_disagreement_terminal_l1
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) :
    |P4AOriginalLicensedSixthSignedLedger.physical
        (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
        N cap w z L (highQTest X F) -
      P4AOriginalLicensedSixthSignedLedger.physical
        (P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ))
        N cap w z L (highQTest X F)| ≤
      actualFirstDisagreementTerminalL1 delta n e q om N cap w z L X F +
      ((rawOutsideHighQInvoice delta e q om N cap w z L X F +
        actualProducerThreeClassLeafBill delta n e q om N cap w z L X F) +
        licensedOutsideHighQInvoice delta n e q om N cap w z L X F) := by
  exact (abs_actual_full_physical_difference_le_stop_and_five_leaf_classes
    delta n e q om N cap w z L X F).trans
    (add_le_add_right
      (abs_actual_stopped_difference_le_first_disagreement_terminal_l1
        delta n e q om N cap w z L X F) _)

end
end ImbalancedChen.P4AOriginalFull87FirstDisagreementTerminalL1
