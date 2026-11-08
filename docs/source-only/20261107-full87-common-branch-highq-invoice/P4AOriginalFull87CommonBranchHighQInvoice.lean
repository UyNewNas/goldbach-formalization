import ImbalancedChen.P4AOriginalFull87SignMatchedTerminalGate
import ImbalancedChen.P4AOriginalFull87PhysicalHighQOwnedInvoice
import ImbalancedChen.P4AOriginalFull87OwnedEighthSource
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

The complete original eighth ordinary comparison is OLD minus NEW,
at ONE history and with ONE literal sign-attached beta terminal.
Previous full87 high-q invoices charged the absolute value of the
whole ordinary saving per occurrence, with no structural account of
shared post-eight continuations. The original policies can agree on
large subtrees even when their sixth parent and eighth cap differ.

This packet inductively cancels BOTH shared skip continuations and
BOTH shared take continuations, charging a take subtree only when
ONE of the original policies actually takes it. This is an exact
signed identity and an explicit nonnegative absolute charge, not
a cap-monotonicity claim, external PP input, or H_N payment.
The original physical test, owner/trim state lists, occurrence
multiplicities, sign and full-q small beta are unchanged.
-/

namespace ImbalancedChen.P4AOriginalFull87CommonBranchHighQInvoice
noncomputable section
open scoped Classical BigOperators
open P1Pair12RetainedSignedSource
open P4AOriginalFull87OwnedEighthSource (ordinarySaving ownedSource)
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87LicensedSixthRealization (states)
open P4AOriginalFull87EighthKernelIntegration (actualParent)
open P4AOriginalFull87SourceDispatch (point8)
open P4AOriginalFull87FiniteEighthCap (finiteCap)
open P4AOriginalFull87PhysicalHighQOwnedInvoice
  (highQTest full87_high_q_gain_eq_owned_sources)
open P4AOriginalFull87LicensedSixthPolicy

/-- The actual old-minus-new signed FIRST-EXIT difference, recursively
retaining shared skip/take histories instead of subtracting independent
unrelated sieves. It uses the ORIGINAL policies and terminal unchanged. -/
def policyDifference {α : Type*} (R S : Bool → List α → Bool)
    (h : α → ℝ) (T : Bool → List α → ℝ)
    (pre : List α) (positive : Bool) (mass : ℝ) : List α → ℝ
  | [] => 0
  | p :: ps =>
      policyDifference R S h T pre positive mass ps +
        (if R (!positive) (p :: pre) = true then
           if S (!positive) (p :: pre) = true then
             policyDifference R S h T (p :: pre) (!positive) (mass * h p) ps
           else signedTest R h T (p :: pre) (!positive) (mass * h p) ps
         else if S (!positive) (p :: pre) = true then
           -(signedTest S h T (p :: pre) (!positive) (mass * h p) ps)
         else 0)

/-- At an unchanged choice, recurse on the ORIGINAL common branch;
at a single-policy take, charge the absolute genuine signed subtree
once and never charge an invented companion subtree. -/
def policyDifferenceCharge {α : Type*} (R S : Bool → List α → Bool)
    (h : α → ℝ) (T : Bool → List α → ℝ)
    (pre : List α) (positive : Bool) (mass : ℝ) : List α → ℝ
  | [] => 0
  | p :: ps =>
      policyDifferenceCharge R S h T pre positive mass ps +
        (if R (!positive) (p :: pre) = true then
           if S (!positive) (p :: pre) = true then
             policyDifferenceCharge R S h T
               (p :: pre) (!positive) (mass * h p) ps
           else |signedTest R h T (p :: pre) (!positive) (mass * h p) ps|
         else if S (!positive) (p :: pre) = true then
           |signedTest S h T (p :: pre) (!positive) (mass * h p) ps|
         else 0)

/-- Exact old-minus-new difference for every terminal arithmetic
test, not just products of independent local weights. A rank-eight
comparison reuses the SAME pre, sign, incoming mass and carrier. -/
theorem policyDifference_eq_signedTest_sub {α : Type*}
    (R S : Bool → List α → Bool) (h : α → ℝ)
    (T : Bool → List α → ℝ)
    (pre remaining : List α) (positive : Bool) (mass : ℝ) :
    policyDifference R S h T pre positive mass remaining =
      signedTest R h T pre positive mass remaining -
        signedTest S h T pre positive mass remaining := by
  induction remaining generalizing pre positive mass with
  | nil => simp [policyDifference, signedTest]
  | cons p ps ih =>
      by_cases hr : R (!positive) (p :: pre) = true
      · by_cases hs : S (!positive) (p :: pre) = true
        · simp only [policyDifference, signedTest, if_pos hr, if_pos hs]
          rw [ih pre positive mass,
            ih (p :: pre) (!positive) (mass * h p)]
          ring
        · simp only [policyDifference, signedTest,
            if_pos hr, if_neg hs, add_zero]
          rw [ih pre positive mass]
          ring
      · by_cases hs : S (!positive) (p :: pre) = true
        · simp only [policyDifference, signedTest,
            if_neg hr, if_pos hs, add_zero]
          rw [ih pre positive mass]
          ring
        · simpa only [policyDifference, signedTest,
            if_neg hr, if_neg hs, add_zero] using
              ih pre positive mass

/-- A genuine absolute invoice for the common-history comparison.
Common skip and common take are not charged twice, and the only
uncancelled whole subtree is taken by exactly one ORIGINAL policy. -/
theorem abs_policyDifference_le_charge {α : Type*}
    (R S : Bool → List α → Bool) (h : α → ℝ)
    (T : Bool → List α → ℝ)
    (pre remaining : List α) (positive : Bool) (mass : ℝ) :
    |policyDifference R S h T pre positive mass remaining| ≤
      policyDifferenceCharge R S h T pre positive mass remaining := by
  induction remaining generalizing pre positive mass with
  | nil => simp [policyDifference, policyDifferenceCharge]
  | cons p ps ih =>
      by_cases hr : R (!positive) (p :: pre) = true
      · by_cases hs : S (!positive) (p :: pre) = true
        · simp only [policyDifference, policyDifferenceCharge,
            if_pos hr, if_pos hs]
          exact (abs_add _ _).trans
            (add_le_add (ih pre positive mass)
              (ih (p :: pre) (!positive) (mass * h p)))
        · simp only [policyDifference, policyDifferenceCharge,
            if_pos hr, if_neg hs]
          exact (abs_add _ _).trans
            (add_le_add_right (ih pre positive mass) _)
      · by_cases hs : S (!positive) (p :: pre) = true
        · simp only [policyDifference, policyDifferenceCharge,
            if_neg hr, if_pos hs]
          calc
            |policyDifference R S h T pre positive mass ps +
                -(signedTest S h T (p :: pre) (!positive) (mass * h p) ps)| ≤
                |policyDifference R S h T pre positive mass ps| +
                  |-(signedTest S h T (p :: pre) (!positive) (mass * h p) ps)| :=
              abs_add _ _
            _ = |policyDifference R S h T pre positive mass ps| +
                  |signedTest S h T (p :: pre) (!positive) (mass * h p) ps| := by
              rw [abs_neg]
            _ ≤ policyDifferenceCharge R S h T pre positive mass ps +
                  |signedTest S h T (p :: pre) (!positive) (mass * h p) ps| :=
              add_le_add_right (ih pre positive mass) _
        · simpa only [policyDifference, policyDifferenceCharge,
            if_neg hr, if_neg hs, add_zero] using
              ih pre positive mass

/-- Stronger than equality of two totals: if the ORIGINAL policies
agree at every extension of this history, the branch invoice itself
vanishes. Equality just at the root would not be sufficient. -/
theorem policyDifferenceCharge_zero_of_extension_agreement {α : Type*}
    (R S : Bool → List α → Bool) (h : α → ℝ)
    (T : Bool → List α → ℝ)
    (pre remaining : List α) (positive : Bool) (mass : ℝ)
    (heq : ∀ later : List α, ∀ b : Bool,
      R b (later ++ pre) = S b (later ++ pre)) :
    policyDifferenceCharge R S h T pre positive mass remaining = 0 := by
  induction remaining generalizing pre positive mass with
  | nil => rfl
  | cons p ps ih =>
      have hnode : R (!positive) (p :: pre) =
          S (!positive) (p :: pre) := by
        simpa only [List.singleton_append] using heq [p] (!positive)
      have hchild : ∀ later : List α, ∀ b : Bool,
          R b (later ++ (p :: pre)) =
          S b (later ++ (p :: pre)) := by
        intro later b
        simpa only [List.append_assoc, List.singleton_append] using
          heq (later ++ [p]) b
      by_cases hr : R (!positive) (p :: pre) = true
      · have hs : S (!positive) (p :: pre) = true := by
          rw [← hnode]
          exact hr
        simp only [policyDifferenceCharge, if_pos hr, if_pos hs]
        rw [ih pre positive mass heq,
          ih (p :: pre) (!positive) (mass * h p) hchild]
        ring
      · have hs : S (!positive) (p :: pre) ≠ true := by
          rw [← hnode]
          exact hr
        simpa only [policyDifferenceCharge, if_neg hr,
          if_neg hs, add_zero] using ih pre positive mass heq

/-- The ORIGINAL two ordinary continuation policies at the same
rank-eight occurrence. This is an abbreviation of their genuine terms,
not a new policy or independent coefficient. -/
def originalSameHistoryHighQCharge
    (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap X : ℕ) (w L : ℝ) (F : ℕ → ℝ)
    (c : Cell) (s : FirstExitDepthState ℕ) : ℝ :=
  policyDifferenceCharge
    (ordinaryParityRosserPolicy false
      ((N : ℝ) ^ actualParent n e q om (N : ℝ) s.selectedPrefix))
    (ordinaryParityRosserPolicy false
      ((N : ℝ) ^ (finiteCap n c
        (point8 (N : ℝ) s.selectedPrefix) : ℝ)))
    (fun _ : ℕ => (1 : ℝ))
    (attachedLeafTest N cap 1 w L (highQTest X F))
    s.selectedPrefix s.positive s.mass s.remaining

/-- The original eighth ordinary saving is the exact recursive
common-history difference, with full physical modulus and genuine
sign-selected Rosser beta at every remaining terminal. -/
theorem original_ordinary_highQ_eq_policyDifference
    (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap X : ℕ) (w L : ℝ) (F : ℕ → ℝ)
    (c : Cell) (s : FirstExitDepthState ℕ) :
    ordinarySaving n e q om N cap w L (highQTest X F) c s =
      policyDifference
        (ordinaryParityRosserPolicy false
          ((N : ℝ) ^ actualParent n e q om (N : ℝ) s.selectedPrefix))
        (ordinaryParityRosserPolicy false
          ((N : ℝ) ^ (finiteCap n c
            (point8 (N : ℝ) s.selectedPrefix) : ℝ)))
        (fun _ : ℕ => (1 : ℝ))
        (attachedLeafTest N cap 1 w L (highQTest X F))
        s.selectedPrefix s.positive s.mass s.remaining := by
  unfold ordinarySaving
  exact (policyDifference_eq_signedTest_sub _ _ _ _ _ _ _ _).symm

/-- This charge is paid against the actual signed old-minus-new
ordinary continuation, not the absolute sums of two unrelated sieves. -/
theorem abs_original_ordinary_highQ_le_common_charge
    (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap X : ℕ) (w L : ℝ) (F : ℕ → ℝ)
    (c : Cell) (s : FirstExitDepthState ℕ) :
    |ordinarySaving n e q om N cap w L (highQTest X F) c s| ≤
      originalSameHistoryHighQCharge n e q om N cap X w L F c s := by
  rw [original_ordinary_highQ_eq_policyDifference]
  exact abs_policyDifference_le_charge _ _ _ _ _ _ _ _

/-- The actual OWNER-filtered eighth source list, not a newly selected
family. Each list occurrence is charged exactly once. -/
def ownedCommonHighQCharge
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (c : Cell) : ℝ :=
  ((states delta n e q om N cap w z (fun _ : ℕ => (1 : ℝ)) c).map
    (originalSameHistoryHighQCharge n e q om N cap X w L F c)).sum

private theorem list_abs_sum_le_common_charge {α : Type*}
    (xs : List α) (f charge : α → ℝ)
    (h : ∀ a ∈ xs, |f a| ≤ charge a) :
    |(xs.map f).sum| ≤ (xs.map charge).sum := by
  induction xs with
  | nil => simp
  | cons x tail ih =>
      have hx := h x (by simp)
      have ht : ∀ y ∈ tail, |f y| ≤ charge y := by
        intro y hy
        exact h y (by simp [hy])
      simp only [List.map_cons, List.sum_cons]
      exact (abs_add _ _).trans (add_le_add hx (ih ht))

/-- Full original87 high-q old-minus-new physical gain, with the
unchanged owner/trim list and all original occurrence multiplicities,
is bounded by ONLY structurally unshared take subtrees. No H_N claim,
PP permission or compiler/density reserve has been used. -/
theorem abs_full87_highQ_le_common_history_invoice
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) :
    |P4AOriginalLicensedSixthSignedLedger.physical
        (sixthPolicy n e q om (N : ℝ)) N cap w z L
          (highQTest X F) -
      P4AOriginalLicensedSixthSignedLedger.physical
        (policy delta n e q om (N : ℝ)) N cap w z L
          (highQTest X F)| ≤
      ∑ c : Cell,
        ownedCommonHighQCharge delta n e q om N cap w z L X F c := by
  rw [full87_high_q_gain_eq_owned_sources]
  calc
    |∑ c : Cell, ownedSource delta n e q om N cap w z L
        (highQTest X F) c| ≤
      ∑ c : Cell,
        |ownedSource delta n e q om N cap w z L
          (highQTest X F) c| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ c : Cell,
        ownedCommonHighQCharge delta n e q om N cap w z L X F c := by
      apply Finset.sum_le_sum
      intro c _
      unfold ownedSource ownedCommonHighQCharge
      exact list_abs_sum_le_common_charge _ _ _
        (fun s _ => abs_original_ordinary_highQ_le_common_charge
          n e q om N cap X w L F c s)

end
end ImbalancedChen.P4AOriginalFull87CommonBranchHighQInvoice
