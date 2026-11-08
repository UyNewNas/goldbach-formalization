import ImbalancedChen.P4AOriginalFull87LicensedOutsideThreeInvoices
import ImbalancedChen.P4AOriginalFull87ExclusiveLeafSignedCut
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

The last three-book conservation charges a matched complete FirstExitDepthState
by |rawSignedHighQ s - licensedSignedHighQ s|.  The present packet expands
THAT actual matched-state charge using the two genuine, DIFFERENT sixth
suffix policies on the SAME selected prefix/sign/mass/remaining carrier.
Only the first exclusive take branches survive.  The original sign-attached
small Rosser beta and STRICT full-modulus high-q predicate remain unchanged.

No claim that a raw occurrence has a licensed partner, that an exclusive
branch is absent in saved87, or that this cost is o(H_N) is made.
-/

namespace ImbalancedChen.P4AOriginalFull87MatchedSuffixDisagreement

noncomputable section
open scoped Classical BigOperators
open P1Pair12RetainedSignedSource (signedTest attachedLeafTest)
open P4AOriginalFull87RawTrimSignedHighQ (rawSignedHighQ)
open P4AOriginalFull87ProducerChangeInvoice (licensedSignedHighQ)
open P4AOriginalFull87ExclusiveLeafSignedCut
  (firstDisagreementLeaves taggedValue taggedHighQTerm exclusiveLeafCost
   policyDifference_eq_firstDisagreementLeaves
   leafHighQTerm_zero_of_active_sign_cut)
open P4AOriginalFull87PhysicalHighQOwnedInvoice
  (highQTest leafHighQTerm abs_leaf_high_q_term_le_charge)

/-- ORIGINAL raw vs NEW licensed, on one IDENTICAL complete state.
The side tag means raw-only or licensed-only; leaf.positive separately
controls the genuine Rosser beta.  This is not the old/new ordinary cap
comparison inside a single filtered parent. -/
def actualMatchedExclusiveLeaves
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N : ℕ) (s : FirstExitDepthState ℕ) :
    List (Bool × FirstExitLeaf ℕ) :=
  firstDisagreementLeaves
    (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
    (P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ))
    (fun _ : ℕ => (1 : ℝ))
    s.selectedPrefix s.positive s.mass s.remaining

/-- This identifies the ACTUAL raw/licensed matched suffix difference
with precisely the first-disagreement physical leaves.  There is one
common terminal T, not a subtraction of unrelated arithmetic means. -/
theorem actual_matched_signed_difference_eq_exclusive
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (s : FirstExitDepthState ℕ) :
    rawSignedHighQ e q om N cap w L X F s -
      licensedSignedHighQ delta n e q om N cap w L X F s =
    ((actualMatchedExclusiveLeaves delta n e q om N s).map
      (taggedHighQTerm N cap w L X F)).sum := by
  unfold rawSignedHighQ licensedSignedHighQ
  rw [← P4AOriginalFull87CommonBranchHighQInvoice.policyDifference_eq_signedTest_sub]
  rw [policyDifference_eq_firstDisagreementLeaves]
  change ((actualMatchedExclusiveLeaves delta n e q om N s).map
    (taggedValue (attachedLeafTest N cap 1 w L (highQTest X F)))).sum =
    ((actualMatchedExclusiveLeaves delta n e q om N s).map
      (taggedHighQTerm N cap w L X F)).sum
  apply congrArg List.sum
  apply List.map_congr_left
  intro t _
  rcases t with ⟨side, leaf⟩
  cases side <;>
    simp [taggedValue, taggedHighQTerm, leafHighQTerm, attachedLeafTest]

/-- An inspectable invoice for matched SAME-state suffix changes.
It does not include raw-only or licensed-only physical occurrences:
those have their own charges in the existing producer ledger. -/
def actualMatchedExclusiveCharge
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (s : FirstExitDepthState ℕ) : ℝ :=
  ((actualMatchedExclusiveLeaves delta n e q om N s).map
    (exclusiveLeafCost N cap w L X F)).sum

private theorem abs_tagged_physical_le_cost
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (tag : Bool × FirstExitLeaf ℕ) :
    |taggedHighQTerm N cap w L X F tag| ≤
      exclusiveLeafCost N cap w L X F tag := by
  rcases tag with ⟨side, leaf⟩
  cases side <;>
    simpa [taggedHighQTerm, exclusiveLeafCost, abs_neg] using
      abs_leaf_high_q_term_le_charge N cap w L X F leaf

/-- A matched ledger item can be invoiced by FIRST divergence,
not by two entire independent signed suffixes.  All List leaf copies
remain present. This is a finite inequality only. -/
theorem abs_actual_matched_difference_le_exclusive_charge
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (s : FirstExitDepthState ℕ) :
    |rawSignedHighQ e q om N cap w L X F s -
       licensedSignedHighQ delta n e q om N cap w L X F s| ≤
    actualMatchedExclusiveCharge delta n e q om N cap w L X F s := by
  rw [actual_matched_signed_difference_eq_exclusive]
  unfold actualMatchedExclusiveCharge
  induction actualMatchedExclusiveLeaves delta n e q om N s with
  | nil => simp
  | cons t ts ih =>
      simp only [List.map_cons, List.sum_cons]
      exact (abs_add _ _).trans
        (add_le_add (abs_tagged_physical_le_cost N cap w L X F t) ih)

/-- A cut is imposed ONLY on actual exclusive leaves, using each
leaf's OWN sign-specific beta, and on the strict physical modulus.
No property of an unrelated shared or inherited branch is required. -/
theorem actual_matched_difference_zero_of_exclusive_active_cut
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (s : FirstExitDepthState ℕ)
    (hcut : ∀ tag ∈ actualMatchedExclusiveLeaves delta n e q om N s,
      ∀ a ∈ actualSmallRosserSupport N cap w,
      (if tag.2.positive then actualSmallRosserPlus N cap w L a
       else actualSmallRosserMinus N cap w L a) ≠ 0 →
       a * tag.2.selected.prod ≤ X) :
    rawSignedHighQ e q om N cap w L X F s -
      licensedSignedHighQ delta n e q om N cap w L X F s = 0 := by
  rw [actual_matched_signed_difference_eq_exclusive]
  have hz :
      ((actualMatchedExclusiveLeaves delta n e q om N s).map
        (taggedHighQTerm N cap w L X F)) =
      (actualMatchedExclusiveLeaves delta n e q om N s).map
        (fun _ => (0 : ℝ)) := by
    apply List.map_congr_left
    intro tag htag
    have hleaf := leafHighQTerm_zero_of_active_sign_cut
      N cap w L X F tag.2 (hcut tag htag)
    cases hs : tag.1 <;>
      simp [taggedHighQTerm, hs, hleaf]
  rw [hz]
  simp

/-- Contrapositive support theorem: a nonzero difference for ONE
actually matched state requires an exclusive retained leaf and a
NONZERO coefficient of its own sign above X.  This is a necessary
witness, not a lower bound on the signed gain. -/
theorem nonzero_matched_difference_has_exclusive_physical_witness
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (s : FirstExitDepthState ℕ)
    (hnz : rawSignedHighQ e q om N cap w L X F s -
      licensedSignedHighQ delta n e q om N cap w L X F s ≠ 0) :
    ∃ tag ∈ actualMatchedExclusiveLeaves delta n e q om N s,
      ∃ a ∈ actualSmallRosserSupport N cap w,
        (if tag.2.positive then actualSmallRosserPlus N cap w L a
         else actualSmallRosserMinus N cap w L a) ≠ 0 ∧
        X < a * tag.2.selected.prod := by
  classical
  by_contra h
  have hcut : ∀ tag ∈ actualMatchedExclusiveLeaves delta n e q om N s,
      ∀ a ∈ actualSmallRosserSupport N cap w,
      (if tag.2.positive then actualSmallRosserPlus N cap w L a
       else actualSmallRosserMinus N cap w L a) ≠ 0 →
       a * tag.2.selected.prod ≤ X := by
    intro tag ht a ha hb
    by_contra hle
    exact h ⟨tag, ht, a, ha, hb, Nat.lt_of_not_ge hle⟩
  exact hnz (actual_matched_difference_zero_of_exclusive_active_cut
    delta n e q om N cap w L X F s hcut)

end
end ImbalancedChen.P4AOriginalFull87MatchedSuffixDisagreement
