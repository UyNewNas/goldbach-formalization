import ImbalancedChen.P4AOriginalFull87CommonBranchHighQInvoice
import ImbalancedChen.P4AOriginalFull87PhysicalHighQOwnedInvoice
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

This refines the preceding SAME-HISTORY policy-difference invoice into a literal
list of first-disagreement retained leaves. A common skip or common take is
traversed once. On the first exclusive take, the whole subtree is enumerated
with its ORIGINAL retained policy, leaf sign and mass; new-only leaves carry
the minus sign of OLD minus NEW.

The resulting finite high-q support certificate checks the *leaf's own*
Rosser beta and strict a*selected.prod > X, not the OR support of both signs.
No physical saved87 row or PP cutoff is supplied or manufactured here.
-/

namespace ImbalancedChen.P4AOriginalFull87ExclusiveLeafSignedCut
noncomputable section
open scoped Classical BigOperators
open P1Pair12RetainedSignedSource
open P4AOriginalFull87CommonBranchHighQInvoice
  (policyDifference original_ordinary_highQ_eq_policyDifference)
open P4AOriginalFull87PhysicalHighQOwnedInvoice
  (highQTest leafHighQTerm leafHighQCharge
   abs_leaf_high_q_term_le_charge full87_high_q_gain_eq_owned_sources)
open P4AOriginalFull87OwnedEighthSource (ordinarySaving ownedSource)
open P4AOriginalFull87LicensedSixthRealization (states)
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87EighthKernelIntegration (actualParent)
open P4AOriginalFull87FiniteEighthCap (finiteCap)
open P4AOriginalFull87SourceDispatch (point8)
open P4AOriginalFull87LicensedSixthPolicy

/-- The Boolean tags identify ORIGINAL old-only and new-only takes,
not the parity of a leaf (which remains leaf.positive). Each LIST item is
one occurrence, even if two physical moduli happen to coincide. -/
def firstDisagreementLeaves {α : Type*}
    (R S : Bool → List α → Bool) (h : α → ℝ)
    (pre : List α) (positive : Bool) (mass : ℝ) :
    List α → List (Bool × FirstExitLeaf α)
  | [] => []
  | p :: ps =>
      firstDisagreementLeaves R S h pre positive mass ps ++
        (if R (!positive) (p :: pre) = true then
          if S (!positive) (p :: pre) = true then
            firstDisagreementLeaves R S h (p :: pre) (!positive) (mass * h p) ps
          else
            (firstExitRetainedLeaves R h (p :: pre) (!positive)
              (mass * h p) ps).map (fun leaf => (true, leaf))
         else if S (!positive) (p :: pre) = true then
           (firstExitRetainedLeaves S h (p :: pre) (!positive)
             (mass * h p) ps).map (fun leaf => (false, leaf))
         else [])

/-- An old-only leaf is added; a new-only leaf is subtracted.
The genuine first-exit leaf sign is *inside* leaf.value and T. -/
def taggedValue {α : Type*} (T : Bool → List α → ℝ)
    (tag : Bool × FirstExitLeaf α) : ℝ :=
  if tag.1 then tag.2.value * T tag.2.positive tag.2.selected
  else -(tag.2.value * T tag.2.positive tag.2.selected)

private theorem list_map_sum_neg {α : Type*}
    (xs : List α) (f : α → ℝ) :
    (xs.map (fun x => -f x)).sum = -(xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      ring

private theorem tagged_old_leaves_eq_signedTest {α : Type*}
    (R : Bool → List α → Bool) (h : α → ℝ)
    (T : Bool → List α → ℝ) (pre remaining : List α)
    (positive : Bool) (mass : ℝ) :
    (((firstExitRetainedLeaves R h pre positive mass remaining).map
      (fun leaf => (true, leaf))).map (taggedValue T)).sum =
      signedTest R h T pre positive mass remaining := by
  rw [signedTest_eq_leaves]
  simp [taggedValue, List.map_map]

private theorem tagged_new_leaves_eq_neg_signedTest {α : Type*}
    (S : Bool → List α → Bool) (h : α → ℝ)
    (T : Bool → List α → ℝ) (pre remaining : List α)
    (positive : Bool) (mass : ℝ) :
    (((firstExitRetainedLeaves S h pre positive mass remaining).map
      (fun leaf => (false, leaf))).map (taggedValue T)).sum =
      -(signedTest S h T pre positive mass remaining) := by
  rw [signedTest_eq_leaves]
  simpa [taggedValue, List.map_map] using
    list_map_sum_neg
      (firstExitRetainedLeaves S h pre positive mass remaining)
      (fun leaf => leaf.value * T leaf.positive leaf.selected)

/-- A FIRST-disagreement identity for an ARBITRARY terminal test.
This proves more than support by cap: shared descendants cancel before
their original signed leaves are enumerated, so they cannot be invoiced. -/
theorem policyDifference_eq_firstDisagreementLeaves {α : Type*}
    (R S : Bool → List α → Bool) (h : α → ℝ)
    (T : Bool → List α → ℝ)
    (pre remaining : List α) (positive : Bool) (mass : ℝ) :
    policyDifference R S h T pre positive mass remaining =
      ((firstDisagreementLeaves R S h pre positive mass remaining).map
        (taggedValue T)).sum := by
  induction remaining generalizing pre positive mass with
  | nil => simp [policyDifference, firstDisagreementLeaves]
  | cons p ps ih =>
      by_cases hr : R (!positive) (p :: pre) = true
      · by_cases hs : S (!positive) (p :: pre) = true
        · simp only [policyDifference, firstDisagreementLeaves,
            if_pos hr, if_pos hs, List.map_append, List.sum_append]
          rw [ih pre positive mass,
            ih (p :: pre) (!positive) (mass * h p)]
        · simp only [policyDifference, firstDisagreementLeaves,
            if_pos hr, if_neg hs, List.map_append, List.sum_append]
          rw [ih pre positive mass,
            tagged_old_leaves_eq_signedTest]
      · by_cases hs : S (!positive) (p :: pre) = true
        · simp only [policyDifference, firstDisagreementLeaves,
            if_neg hr, if_pos hs, List.map_append, List.sum_append]
          rw [ih pre positive mass,
            tagged_new_leaves_eq_neg_signedTest]
        · simpa only [policyDifference, firstDisagreementLeaves,
            if_neg hr, if_neg hs, add_zero, List.append_nil] using
              ih pre positive mass

/-- Physical high-q term of the tagged occurrence, using the ORIGINAL
leaf's parity, small beta and complete modulus. -/
def taggedHighQTerm (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (F : ℕ → ℝ) (tag : Bool × FirstExitLeaf ℕ) : ℝ :=
  if tag.1 then leafHighQTerm N cap w L X F tag.2
  else -leafHighQTerm N cap w L X F tag.2

private theorem taggedValue_attached_eq_highQ
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (tag : Bool × FirstExitLeaf ℕ) :
    taggedValue (attachedLeafTest N cap 1 w L (highQTest X F)) tag =
      taggedHighQTerm N cap w L X F tag := by
  rcases tag with ⟨side, leaf⟩
  cases side <;>
    simp [taggedValue, taggedHighQTerm, leafHighQTerm, attachedLeafTest]

/-- Only the ORIGINAL two policies, original common prefix and full
sign-selected Rosser coefficient can produce this tagged occurrence list. -/
def originalExclusiveLeaves
    (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N : ℕ) (c : Cell) (s : FirstExitDepthState ℕ) :
    List (Bool × FirstExitLeaf ℕ) :=
  firstDisagreementLeaves
    (ordinaryParityRosserPolicy false
      ((N : ℝ) ^ actualParent n e q om (N : ℝ) s.selectedPrefix))
    (ordinaryParityRosserPolicy false
      ((N : ℝ) ^ (finiteCap n c
        (point8 (N : ℝ) s.selectedPrefix) : ℝ)))
    (fun _ : ℕ => (1 : ℝ))
    s.selectedPrefix s.positive s.mass s.remaining

/-- No new physical coefficient: exact expansion of the original ordinary
old-minus-new high-q term into first-disagreement retained leaf occurrences. -/
theorem original_ordinary_highQ_eq_exclusive_leaf_sum
    (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap X : ℕ) (w L : ℝ) (F : ℕ → ℝ)
    (c : Cell) (s : FirstExitDepthState ℕ) :
    ordinarySaving n e q om N cap w L (highQTest X F) c s =
      ((originalExclusiveLeaves n e q om N c s).map
        (taggedHighQTerm N cap w L X F)).sum := by
  rw [original_ordinary_highQ_eq_policyDifference]
  rw [policyDifference_eq_firstDisagreementLeaves]
  simp_rw [taggedValue_attached_eq_highQ]
  rfl

/-- The true sign-restricted support is sufficient to make ONE retained
leaf's complete high-q contribution zero. It is NOT necessary to bound
display-only factors whose actual sign beta vanishes. -/
theorem leafHighQTerm_zero_of_active_sign_cut
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (leaf : FirstExitLeaf ℕ)
    (hcut : ∀ a ∈ actualSmallRosserSupport N cap w,
      (if leaf.positive then actualSmallRosserPlus N cap w L a
       else actualSmallRosserMinus N cap w L a) ≠ 0 →
        a * leaf.selected.prod ≤ X) :
    leafHighQTerm N cap w L X F leaf = 0 := by
  unfold leafHighQTerm
  have hz : (∑ a ∈ actualSmallRosserSupport N cap w,
      (if leaf.positive then actualSmallRosserPlus N cap w L a
       else actualSmallRosserMinus N cap w L a) *
        highQTest X F (a * leaf.selected.prod)) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    by_cases hb : (if leaf.positive then actualSmallRosserPlus N cap w L a
      else actualSmallRosserMinus N cap w L a) = 0
    · simp [hb]
    · have hle := hcut a ha hb
      simp [highQTest, Nat.not_lt.mpr hle]
  rw [hz, mul_zero]

/-- Only exclusive retained leaves with an actually nonzero,
parity-matched small beta need to pass the physical cutoff. Shared
branches, which are absent from this LIST, need not pass any check. -/
theorem original_ordinary_highQ_zero_of_exclusive_active_cut
    (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap X : ℕ) (w L : ℝ) (F : ℕ → ℝ)
    (c : Cell) (s : FirstExitDepthState ℕ)
    (hcut : ∀ t ∈ originalExclusiveLeaves n e q om N c s,
      ∀ a ∈ actualSmallRosserSupport N cap w,
      (if t.2.positive then actualSmallRosserPlus N cap w L a
       else actualSmallRosserMinus N cap w L a) ≠ 0 →
        a * t.2.selected.prod ≤ X) :
    ordinarySaving n e q om N cap w L (highQTest X F) c s = 0 := by
  rw [original_ordinary_highQ_eq_exclusive_leaf_sum]
  have hz : ((originalExclusiveLeaves n e q om N c s).map
        (taggedHighQTerm N cap w L X F)) =
      (originalExclusiveLeaves n e q om N c s).map (fun _ => (0 : ℝ)) := by
    apply List.map_congr_left
    intro t ht
    have htzero := leafHighQTerm_zero_of_active_sign_cut
      N cap w L X F t.2 (hcut t ht)
    cases htSide : t.1 <;>
      simp [taggedHighQTerm, htSide, htzero]
  rw [hz]
  simp

/-- An explicitly inspectable per-first-divergence-leaf absolute charge.
The old/new side tag affects the SIGN, not the absolute physical cost. -/
def exclusiveLeafCost (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (F : ℕ → ℝ) (tag : Bool × FirstExitLeaf ℕ) : ℝ :=
  leafHighQCharge N cap w L X F tag.2

private theorem abs_taggedHighQTerm_le_cost
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (tag : Bool × FirstExitLeaf ℕ) :
    |taggedHighQTerm N cap w L X F tag| ≤
      exclusiveLeafCost N cap w L X F tag := by
  rcases tag with ⟨side, leaf⟩
  cases side <;>
    simpa [taggedHighQTerm, exclusiveLeafCost, abs_neg] using
      abs_leaf_high_q_term_le_charge N cap w L X F leaf

private theorem abs_tagged_sum_le_cost
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (xs : List (Bool × FirstExitLeaf ℕ)) :
    |(xs.map (taggedHighQTerm N cap w L X F)).sum| ≤
      (xs.map (exclusiveLeafCost N cap w L X F)).sum := by
  induction xs with
  | nil => simp
  | cons t xs ih =>
      simp only [List.map_cons, List.sum_cons]
      exact (abs_add _ _).trans
        (add_le_add (abs_taggedHighQTerm_le_cost N cap w L X F t) ih)

/-- An explicit ORIGINAL tagged exclusive-leaf invoice for one actual
rank-eight occurrence, with all original small-beta and leaf multiplicity. -/
theorem abs_original_ordinary_highQ_le_exclusive_cost
    (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap X : ℕ) (w L : ℝ) (F : ℕ → ℝ)
    (c : Cell) (s : FirstExitDepthState ℕ) :
    |ordinarySaving n e q om N cap w L (highQTest X F) c s| ≤
      ((originalExclusiveLeaves n e q om N c s).map
        (exclusiveLeafCost N cap w L X F)).sum := by
  rw [original_ordinary_highQ_eq_exclusive_leaf_sum]
  exact abs_tagged_sum_le_cost N cap w L X F _

/-- Complete original owner/trim list. This map preserves occurrences,
including duplicates. No Finset conversion of states occurs. -/
def ownedExclusiveLeafCost
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (c : Cell) : ℝ :=
  ((states delta n e q om N cap w z (fun _ : ℕ => (1 : ℝ)) c).map
    (fun s => ((originalExclusiveLeaves n e q om N c s).map
      (exclusiveLeafCost N cap w L X F)).sum)).sum

private theorem list_abs_sum_le_cost {α : Type*}
    (xs : List α) (f cost : α → ℝ)
    (h : ∀ x ∈ xs, |f x| ≤ cost x) :
    |(xs.map f).sum| ≤ (xs.map cost).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx := h x (by simp)
      have ht : ∀ y ∈ xs, |f y| ≤ cost y := by
        intro y hy
        exact h y (by simp [hy])
      simp only [List.map_cons, List.sum_cons]
      exact (abs_add _ _).trans (add_le_add hx (ih ht))

/-- Finite physical full87 HIGH-q difference bound on the original
owner-filtered sixth/eighth policies. Only first-disagreement leaf
occurrences can contribute. Still no asymptotic H_N payment or PP license. -/
theorem abs_full87_highQ_le_exclusive_leaf_invoice
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) :
    |P4AOriginalLicensedSixthSignedLedger.physical
      (sixthPolicy n e q om (N : ℝ)) N cap w z L (highQTest X F) -
     P4AOriginalLicensedSixthSignedLedger.physical
      (policy delta n e q om (N : ℝ)) N cap w z L (highQTest X F)| ≤
      ∑ c : Cell,
        ownedExclusiveLeafCost delta n e q om N cap w z L X F c := by
  rw [full87_high_q_gain_eq_owned_sources]
  calc
    |∑ c : Cell, ownedSource delta n e q om N cap w z L
      (highQTest X F) c| ≤
        ∑ c : Cell,
          |ownedSource delta n e q om N cap w z L
            (highQTest X F) c| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ c : Cell,
          ownedExclusiveLeafCost delta n e q om N cap w z L X F c := by
      apply Finset.sum_le_sum
      intro c _
      unfold ownedSource ownedExclusiveLeafCost
      exact list_abs_sum_le_cost _ _ _
        (fun s _ => abs_original_ordinary_highQ_le_exclusive_cost
          n e q om N cap X w L F c s)

end
end ImbalancedChen.P4AOriginalFull87ExclusiveLeafSignedCut
