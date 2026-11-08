import ImbalancedChen.P4AOriginalFull87FifthSixthStoppedEvents
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

Actual rank-seven exhaustion of the two-sided early-stop difference.
The two policies first agree at rank four, and have independently tested
fifth/sixth/seventh gates. A rank-seven BOTH child cannot contribute a
stopped-before-eight difference: every possible rank-eight child is
excluded by stoppedTest 8, and the common rank-seven terminal remains.
Thus its signed stopped difference is EXACTLY ZERO, not an assumed
smallness estimate or a cap-monotonicity claim.

The only remaining early-stop event sources are one-sided admitted gates
at ranks five, six, seven. Fifth/sixth exclusive subtrees are retained,
while seventh exclusive values become the literal signed terminal leaf
with the original full-modulus small-Rosser attachment. No occurrence
is combined or masked with a different later policy.
-/

namespace ImbalancedChen.P4AOriginalFull87SeventhExhaustion
noncomputable section
open scoped Classical BigOperators
open P1Pair12RetainedSignedSource
  (stoppedTest attachedLeafTest)
open P4AOriginalFull87PhysicalHighQOwnedInvoice (highQTest)
open P4AOriginalFull87FirstFifthStoppedEvents
  (FifthStoppedEvent FifthAdmissionClass)
open P4AOriginalFull87RankFourStoppedLocalization
  (sharedRankFour actual_stopped_difference_eq_shared_four_suffix)
open P4AOriginalFull87EarlyStopPhysicalGap
  (rawStopped licensedStopped
   abs_actual_full_physical_difference_le_stop_and_five_leaf_classes)
open P4AOriginalFull87RawTrimSignedHighQ (rawOutsideHighQInvoice)
open P4AOriginalFull87LicensedOutsideThreeInvoices (licensedOutsideHighQInvoice)
open P4AOriginalFull87ThreeClassLeafInvoices (actualProducerThreeClassLeafBill)

/-- At and after depth eight the stopped recursion is identically zero,
regardless of admission decisions or the remaining carrier. -/
theorem stopped_zero_from_eight {α : Type*}
    (R : Bool → List α → Bool) (h : α → ℝ)
    (T : Bool → List α → ℝ) (pre : List α)
    (positive : Bool) (mass : ℝ) (remaining : List α)
    (hdepth : 8 ≤ pre.length) :
    stoppedTest 8 R h T pre positive mass remaining = 0 := by
  cases remaining with
  | nil => simp [stoppedTest, hdepth]
  | cons p ps => simp [stoppedTest, hdepth]

/-- Any accepted seventh-ranked prefix has a policy-INDEPENDENT stopped
value. Even when the carrier still contains further primes, all eighth
children are identically zero. The skip path ends at the SAME terminal. -/
theorem stopped_seven_eq_literal_terminal {α : Type*}
    (R : Bool → List α → Bool) (h : α → ℝ)
    (T : Bool → List α → ℝ) (pre : List α)
    (positive : Bool) (mass : ℝ) (remaining : List α)
    (hdepth : pre.length = 7) :
    stoppedTest 8 R h T pre positive mass remaining =
      signedTreeCoefficient positive mass * T positive pre := by
  induction remaining with
  | nil =>
      have hk : ¬ 8 ≤ pre.length := by omega
      simp [stoppedTest, hk]
  | cons p ps ih =>
      have hk : ¬ 8 ≤ pre.length := by omega
      have hchild : 8 ≤ (p :: pre).length := by simp [hdepth]
      have hz := stopped_zero_from_eight R h T (p :: pre)
        (!positive) (mass * h p) ps hchild
      simp only [stoppedTest, if_neg hk]
      rw [hz, ih]
      simp

/-- The seventh event is exclusive only; BOTH is deliberately absent.
The value at this rank is the ACTUAL exhausted rank-seven signed leaf,
not an opaque policy-dependent continuation or a new coefficient. -/
def seventhExclusiveEvents {α : Type*}
    (R S : Bool → List α → Bool) (h : α → ℝ)
    (T : Bool → List α → ℝ)
    (pre : List α) (positive : Bool) (mass : ℝ) :
    List α → List (FifthStoppedEvent α)
  | [] => []
  | p :: ps =>
      let child := p :: pre
      let sign := !positive
      let childMass := mass * h p
      let terminal := signedTreeCoefficient sign childMass * T sign child
      let emit (kind : FifthAdmissionClass) (value : ℝ) :
          List (FifthStoppedEvent α) :=
        [⟨child, sign, childMass, ps, kind, value⟩]
      let now :=
        if R sign child = true then
          if S sign child = true then []
          else emit .rawOnly terminal
        else if S sign child = true then
          emit .licensedOnly (-terminal)
        else []
      now ++ seventhExclusiveEvents R S h T pre positive mass ps

/-- At a genuine sixth prefix, only EXCLUSIVELY admitted seventh
candidates can change the stopped-before-eight sum. Both-admitted
seventh children cancel algebraically by the literal-terminal theorem.
The induction scans the ORIGINAL ordered tail, keeping repetitions. -/
theorem stopped_difference_eq_seventh_exclusives {α : Type*}
    (R S : Bool → List α → Bool) (h : α → ℝ)
    (T : Bool → List α → ℝ)
    (pre : List α) (positive : Bool) (mass : ℝ)
    (remaining : List α) (hpre : pre.length = 6) :
    stoppedTest 8 R h T pre positive mass remaining -
      stoppedTest 8 S h T pre positive mass remaining =
    ((seventhExclusiveEvents R S h T pre positive mass remaining).map
      (fun event => event.signedValue)).sum := by
  induction remaining with
  | nil =>
      have hk : ¬ 8 ≤ pre.length := by omega
      simp [stoppedTest, seventhExclusiveEvents, hk]
  | cons p ps ih =>
      have hk : ¬ 8 ≤ pre.length := by omega
      have h7 : (p :: pre).length = 7 := by simp [hpre]
      have hr7 := stopped_seven_eq_literal_terminal R h T
        (p :: pre) (!positive) (mass * h p) ps h7
      have hs7 := stopped_seven_eq_literal_terminal S h T
        (p :: pre) (!positive) (mass * h p) ps h7
      cases hr : R (!positive) (p :: pre) <;>
        cases hs : S (!positive) (p :: pre) <;>
        simp [stoppedTest, seventhExclusiveEvents,
          hk, hr, hs, hr7, hs7, List.map_append, List.sum_append] <;>
        linarith only [ih]

/-- A sixth-only admission pays its own stopped subtree. The sixth
BOTH child is EXPANDED into genuine seventh-exclusive terminal leaves;
there is no sixth-BOTH fee retained a second time. -/
inductive SixthSeventhEvent (α : Type*) where
  | sixthExclusive (event : FifthStoppedEvent α)
  | seventhAfterBoth (sixthSelected : List α) (event : FifthStoppedEvent α)

def SixthSeventhEvent.signedValue {α : Type*} :
    SixthSeventhEvent α → ℝ
  | .sixthExclusive e => e.signedValue
  | .seventhAfterBoth _ e => e.signedValue

def sixthThenSeventhEvents {α : Type*}
    (R S : Bool → List α → Bool) (h : α → ℝ)
    (T : Bool → List α → ℝ)
    (pre : List α) (positive : Bool) (mass : ℝ) :
    List α → List (SixthSeventhEvent α)
  | [] => []
  | p :: ps =>
      let child := p :: pre
      let sign := !positive
      let childMass := mass * h p
      let rawChild := stoppedTest 8 R h T child sign childMass ps
      let licChild := stoppedTest 8 S h T child sign childMass ps
      let emit (kind : FifthAdmissionClass) (value : ℝ) :
          List (SixthSeventhEvent α) :=
        [.sixthExclusive ⟨child, sign, childMass, ps, kind, value⟩]
      let now :=
        if R sign child = true then
          if S sign child = true then
            (seventhExclusiveEvents R S h T child sign childMass ps).map
              (SixthSeventhEvent.seventhAfterBoth child)
          else emit .rawOnly rawChild
        else if S sign child = true then
          emit .licensedOnly (-licChild)
        else []
      now ++ sixthThenSeventhEvents R S h T pre positive mass ps

theorem stopped_difference_eq_sixth_seventh_events {α : Type*}
    (R S : Bool → List α → Bool) (h : α → ℝ)
    (T : Bool → List α → ℝ)
    (pre : List α) (positive : Bool) (mass : ℝ)
    (remaining : List α) (hpre : pre.length = 5) :
    stoppedTest 8 R h T pre positive mass remaining -
      stoppedTest 8 S h T pre positive mass remaining =
    ((sixthThenSeventhEvents R S h T pre positive mass remaining).map
      SixthSeventhEvent.signedValue).sum := by
  induction remaining with
  | nil =>
      have hk : ¬ 8 ≤ pre.length := by omega
      simp [stoppedTest, sixthThenSeventhEvents, hk]
  | cons p ps ih =>
      have hk : ¬ 8 ≤ pre.length := by omega
      have hchild :
          stoppedTest 8 R h T (p :: pre) (!positive) (mass * h p) ps -
          stoppedTest 8 S h T (p :: pre) (!positive) (mass * h p) ps =
          ((seventhExclusiveEvents R S h T (p :: pre) (!positive)
              (mass * h p) ps).map
            (fun event => event.signedValue)).sum :=
        stopped_difference_eq_seventh_exclusives R S h T
          (p :: pre) (!positive) (mass * h p) ps (by simp [hpre])
      cases hr : R (!positive) (p :: pre) <;>
        cases hs : S (!positive) (p :: pre) <;>
        simp [stoppedTest, sixthThenSeventhEvents,
          SixthSeventhEvent.signedValue, hk, hr, hs,
          List.map_append, List.map_map, List.sum_append] <;>
        linarith only [ih, hchild]

/-- At the original shared fourth history, fifth-exclusive events stay
at fifth rank. Only fifth BOTH candidates enter the actual sixth tail;
only sixth BOTH candidates enter the actual seventh terminal scan. -/
inductive FifthSixthSeventhEvent (α : Type*) where
  | fifthExclusive (event : FifthStoppedEvent α)
  | afterBothFifth (fifthSelected : List α) (event : SixthSeventhEvent α)

def FifthSixthSeventhEvent.signedValue {α : Type*} :
    FifthSixthSeventhEvent α → ℝ
  | .fifthExclusive e => e.signedValue
  | .afterBothFifth _ e => e.signedValue

def fifthThenSixthSeventhEvents {α : Type*}
    (R S : Bool → List α → Bool) (h : α → ℝ)
    (T : Bool → List α → ℝ)
    (pre : List α) (positive : Bool) (mass : ℝ) :
    List α → List (FifthSixthSeventhEvent α)
  | [] => []
  | p :: ps =>
      let child := p :: pre
      let sign := !positive
      let childMass := mass * h p
      let rawChild := stoppedTest 8 R h T child sign childMass ps
      let licChild := stoppedTest 8 S h T child sign childMass ps
      let emit (kind : FifthAdmissionClass) (value : ℝ) :
          List (FifthSixthSeventhEvent α) :=
        [.fifthExclusive ⟨child, sign, childMass, ps, kind, value⟩]
      let now :=
        if R sign child = true then
          if S sign child = true then
            (sixthThenSeventhEvents R S h T child sign childMass ps).map
              (FifthSixthSeventhEvent.afterBothFifth child)
          else emit .rawOnly rawChild
        else if S sign child = true then
          emit .licensedOnly (-licChild)
        else []
      now ++ fifthThenSixthSeventhEvents R S h T pre positive mass ps

theorem stopped_difference_eq_fifth_sixth_seventh_events {α : Type*}
    (R S : Bool → List α → Bool) (h : α → ℝ)
    (T : Bool → List α → ℝ)
    (pre : List α) (positive : Bool) (mass : ℝ)
    (remaining : List α) (hpre : pre.length = 4) :
    stoppedTest 8 R h T pre positive mass remaining -
      stoppedTest 8 S h T pre positive mass remaining =
    ((fifthThenSixthSeventhEvents R S h T pre positive mass remaining).map
      FifthSixthSeventhEvent.signedValue).sum := by
  induction remaining with
  | nil =>
      have hk : ¬ 8 ≤ pre.length := by omega
      simp [stoppedTest, fifthThenSixthSeventhEvents, hk]
  | cons p ps ih =>
      have hk : ¬ 8 ≤ pre.length := by omega
      have hchild :
          stoppedTest 8 R h T (p :: pre) (!positive) (mass * h p) ps -
          stoppedTest 8 S h T (p :: pre) (!positive) (mass * h p) ps =
          ((sixthThenSeventhEvents R S h T (p :: pre) (!positive)
              (mass * h p) ps).map
            SixthSeventhEvent.signedValue).sum :=
        stopped_difference_eq_sixth_seventh_events R S h T
          (p :: pre) (!positive) (mass * h p) ps (by simp [hpre])
      cases hr : R (!positive) (p :: pre) <;>
        cases hs : S (!positive) (p :: pre) <;>
        simp [stoppedTest, fifthThenSixthSeventhEvents,
          FifthSixthSeventhEvent.signedValue, hk, hr, hs,
          List.map_append, List.map_map, List.sum_append] <;>
        linarith only [ih, hchild]

/-- Actual full-modulus high-q terminal. The only small coefficients are
the original sign-dependent Rosser beta at the physical modulus a*prod. -/
theorem seventh_terminal_zero_below_full_modulus
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (pre : List ℕ) (positive : Bool) (mass : ℝ)
    (hsmall : ∀ a ∈ actualSmallRosserSupport N cap w,
      a * pre.prod ≤ X) :
    signedTreeCoefficient positive mass *
      attachedLeafTest N cap 1 w L (highQTest X F) positive pre = 0 := by
  have hzero : attachedLeafTest N cap 1 w L
      (highQTest X F) positive pre = 0 := by
    unfold attachedLeafTest
    apply Finset.sum_eq_zero
    intro a ha
    have hnot : ¬ X < a * pre.prod := Nat.not_lt.mpr (hsmall a ha)
    simp [highQTest, hnot]
  rw [hzero, mul_zero]

/-- A nonzero rank-seven exclusive leaf requires a REAL small-Rosser
factor with nonzero signed beta AND a STRICTLY large complete q.
This is a necessary witness, not a uniform count or an o(H_N) bound. -/
theorem seventh_terminal_nonzero_has_physical_highq_witness
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (pre : List ℕ) (positive : Bool) (mass : ℝ)
    (hnz : signedTreeCoefficient positive mass *
      attachedLeafTest N cap 1 w L (highQTest X F) positive pre ≠ 0) :
    ∃ a ∈ actualSmallRosserSupport N cap w,
      X < a * pre.prod ∧
      (if positive then actualSmallRosserPlus N cap w L a
       else actualSmallRosserMinus N cap w L a) ≠ 0 ∧
      F (a * pre.prod) ≠ 0 := by
  have hattached : attachedLeafTest N cap 1 w L
      (highQTest X F) positive pre ≠ 0 := by
    intro hzero
    exact hnz (by simp [hzero])
  have hex : ∃ a ∈ actualSmallRosserSupport N cap w,
      (if positive then actualSmallRosserPlus N cap w L a
       else actualSmallRosserMinus N cap w L a) *
        highQTest X F (a * pre.prod) ≠ 0 := by
    by_contra hno
    have hz : attachedLeafTest N cap 1 w L
        (highQTest X F) positive pre = 0 := by
      unfold attachedLeafTest
      apply Finset.sum_eq_zero
      intro a ha
      by_contra hterm
      exact hno ⟨a, ha, hterm⟩
    exact hattached hz
  rcases hex with ⟨a, ha, hv⟩
  by_cases hcut : X < a * pre.prod
  · have hb : (if positive then actualSmallRosserPlus N cap w L a
        else actualSmallRosserMinus N cap w L a) ≠ 0 := by
      intro hb
      exact hv (by simp [hb])
    have hF : F (a * pre.prod) ≠ 0 := by
      intro hf
      exact hv (by simp [highQTest, hcut, hf])
    exact ⟨a, ha, hcut, hb, hF⟩
  · exact False.elim (hv (by simp [highQTest, hcut]))

/-- Original complete-sixth and licensed-sixth are evaluated at the
SAME REAL shared rank-four occurrence, with exact post-occurrence tail. -/
def actualFifthSixthSeventhEvents
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (state : FirstExitDepthState ℕ) : List (FifthSixthSeventhEvent ℕ) :=
  fifthThenSixthSeventhEvents
    (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
    (P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ))
    (fun _ : ℕ => (1 : ℝ))
    (attachedLeafTest N cap 1 w L (highQTest X F))
    state.selectedPrefix state.positive state.mass state.remaining

theorem actual_stopped_difference_eq_exclusive_five_six_seven
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) :
    rawStopped e q om N cap w z L X F -
      licensedStopped delta n e q om N cap w z L X F =
    ((sharedRankFour e q om N cap w z).map (fun state =>
      ((actualFifthSixthSeventhEvents delta n e q om N cap w L X F state).map
        FifthSixthSeventhEvent.signedValue).sum)).sum := by
  rw [actual_stopped_difference_eq_shared_four_suffix]
  apply congrArg List.sum
  apply List.map_congr_left
  intro state hs
  have hlen : state.selectedPrefix.length = 4 :=
    firstExitDepthFrontier_selected_length 4
      (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
      (fun _ : ℕ => (1 : ℝ)) []
      (roughPrimeUniverse N cap w z) true 1 (by simp) state hs
  exact stopped_difference_eq_fifth_sixth_seventh_events
    (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
    (P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ))
    (fun _ : ℕ => (1 : ℝ))
    (attachedLeafTest N cap 1 w L (highQTest X F))
    state.selectedPrefix state.positive state.mass state.remaining hlen

private theorem abs_nested_map_sum_le {α β : Type*}
    (xs : List α) (g : α → List β) (f : β → ℝ) :
    |(xs.map (fun x => ((g x).map f).sum)).sum| ≤
      (xs.map (fun x => ((g x).map (fun t => |f t|)).sum)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      have hfirst :
          |((g x).map f).sum| ≤
            ((g x).map (fun t => |f t|)).sum := by
        induction (g x) with
        | nil => simp
        | cons y ys ihy =>
            simp only [List.map_cons, List.sum_cons]
            exact (abs_add _ _).trans (add_le_add_left ihy _)
      exact (abs_add _ _).trans (add_le_add hfirst ih)

/-- Single-payment early stop invoice: fifth exclusive subtrees,
sixth exclusive subtrees under fifth BOTH, and seventh literal
terminal leaves under fifth/sixth BOTH. Seventh BOTH costs ZERO. -/
def actualExclusiveFiveSixSevenInvoice
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) : ℝ :=
  ((sharedRankFour e q om N cap w z).map (fun state =>
    ((actualFifthSixthSeventhEvents delta n e q om N cap w L X F state).map
      (fun event => |event.signedValue|)).sum)).sum

theorem abs_stopped_delta_le_exclusive_five_six_seven
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) :
    |rawStopped e q om N cap w z L X F -
      licensedStopped delta n e q om N cap w z L X F| ≤
    actualExclusiveFiveSixSevenInvoice delta n e q om N cap w z L X F := by
  rw [actual_stopped_difference_eq_exclusive_five_six_seven]
  exact abs_nested_map_sum_le (sharedRankFour e q om N cap w z)
    (actualFifthSixthSeventhEvents delta n e q om N cap w L X F)
    FifthSixthSeventhEvent.signedValue

/-- The rank-seven closed invoice REPLACES the previous fifth/sixth
early-stop invoice. The five existing frontier classes remain once.
No same-rho/H_N bound is asserted, even for the rank-seven terms. -/
theorem abs_full_physical_le_exclusive_seventh_and_five_frontier_classes
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) :
    |P4AOriginalLicensedSixthSignedLedger.physical
        (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
        N cap w z L (highQTest X F) -
      P4AOriginalLicensedSixthSignedLedger.physical
        (P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ))
        N cap w z L (highQTest X F)| ≤
    actualExclusiveFiveSixSevenInvoice delta n e q om N cap w z L X F +
      ((rawOutsideHighQInvoice delta e q om N cap w z L X F +
        actualProducerThreeClassLeafBill delta n e q om N cap w z L X F) +
        licensedOutsideHighQInvoice delta n e q om N cap w z L X F) := by
  exact (abs_actual_full_physical_difference_le_stop_and_five_leaf_classes
    delta n e q om N cap w z L X F).trans
    (add_le_add_right
      (abs_stopped_delta_le_exclusive_five_six_seven
        delta n e q om N cap w z L X F) _)

end
end ImbalancedChen.P4AOriginalFull87SeventhExhaustion
