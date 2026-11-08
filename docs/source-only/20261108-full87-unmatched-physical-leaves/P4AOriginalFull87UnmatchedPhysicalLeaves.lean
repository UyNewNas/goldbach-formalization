import ImbalancedChen.P4AOriginalFull87ExclusiveLedgerThreeInvoices
import ImbalancedChen.P4AOriginalFull87PhysicalHighQOwnedInvoice
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
The previous one-copy producer invoice is cost-only. Here the original RAW
and genuine LICENSED unmatched full states are materialized as separate
physical retained-leaf lists. Matched copies alone use the shared history's
first-exclusive leaves. No owner/trim, sign, multiplicity, beta, or strict
X < a * selected.prod modulus is discarded. This is a finite signed
identity, not a saved87 witness, a PP estimate, or an H_N payment.
-/

namespace ImbalancedChen.P4AOriginalFull87UnmatchedPhysicalLeaves
noncomputable section
open scoped Classical BigOperators
open P1Pair12RetainedSignedSource (signedTest_eq_leaves attachedLeafTest)
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87RawTrimSignedHighQ (rawSignedHighQ rawOwnedTrimmed)
open P4AOriginalFull87ProducerChangeInvoice
  (licensedSignedHighQ actualCellLedger producerLedger_signed)
open P4AOriginalFull87LicensedSixthRealization (states)
open P4AOriginalFull87MatchedSuffixDisagreement
  (actualMatchedExclusiveLeaves actual_matched_signed_difference_eq_exclusive)
open P4AOriginalFull87ExclusiveLeafSignedCut
  (taggedHighQTerm leafHighQTerm_zero_of_active_sign_cut)
open P4AOriginalFull87PhysicalHighQOwnedInvoice
  (leafHighQTerm highQTest)

/-- Remove exactly ONE matching complete-state copy. -/
private def removeOne {α : Type*} [DecidableEq α] (x : α) : List α → List α
  | [] => []
  | y :: ys => if y = x then ys else y :: removeOne x ys

private theorem removeOne_sum {α : Type*} [DecidableEq α]
    (x : α) (ys : List α) (g : α → ℝ) (hx : x ∈ ys) :
    (ys.map g).sum = g x + ((removeOne x ys).map g).sum := by
  induction ys with
  | nil => cases hx
  | cons y ys ih =>
      by_cases h : y = x
      · subst y
        simp [removeOne]
      · have ht : x ∈ ys := by simpa [h] using hx
        have he := ih ht
        rw [show removeOne x (y :: ys) = y :: removeOne x ys by
          simp [removeOne, h]]
        simp only [List.map_cons, List.sum_cons]
        rw [he]
        ring

/-- fst is matched full-state copies; snd.fst is raw-only;
snd.snd is licensed-only. Repeated full states are paired once each. -/
def pairedCopies {α : Type*} [DecidableEq α] :
    List α → List α → List α × List α × List α
  | [], ys => ([], [], ys)
  | x :: xs, ys =>
      if x ∈ ys then
        let t := pairedCopies xs (removeOne x ys)
        (x :: t.1, t.2.1, t.2.2)
      else
        let t := pairedCopies xs ys
        (t.1, x :: t.2.1, t.2.2)

/-- Exact signed three-way conservation, without Nodup or equality of
the two actual producers. A matched state pays f(x)-g(x), not zero. -/
theorem pairedCopies_signed {α : Type*} [DecidableEq α]
    (f g : α → ℝ) (xs ys : List α) :
    (xs.map f).sum - (ys.map g).sum =
      (((pairedCopies xs ys).1).map (fun s => f s - g s)).sum +
      (((pairedCopies xs ys).2.1).map f).sum -
      (((pairedCopies xs ys).2.2).map g).sum := by
  induction xs generalizing ys with
  | nil => simp [pairedCopies]
  | cons x xs ih =>
      by_cases hx : x ∈ ys
      · have he := removeOne_sum x ys g hx
        have ht := ih (removeOne x ys)
        simp only [pairedCopies, if_pos hx, List.map_cons, List.sum_cons,
          Prod.fst, Prod.snd]
        rw [he]
        linarith
      · have ht := ih ys
        simp only [pairedCopies, if_neg hx, List.map_cons, List.sum_cons,
          Prod.fst, Prod.snd]
        linarith

/-- The complete original sixth policy's actual retained suffix leaves. -/
def rawRetainedLeaves (e : ℚ) (q : ℕ) (om : ℝ) (N : ℕ)
    (s : FirstExitDepthState ℕ) : List (FirstExitLeaf ℕ) :=
  firstExitRetainedLeaves
    (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
    (fun _ : ℕ => (1 : ℝ))
    s.selectedPrefix s.positive s.mass s.remaining

/-- The different licensed sixth policy's retained suffix leaves. -/
def licensedRetainedLeaves (delta : ℝ) (n : ℕ) (e : ℚ)
    (q : ℕ) (om : ℝ) (N : ℕ)
    (s : FirstExitDepthState ℕ) : List (FirstExitLeaf ℕ) :=
  firstExitRetainedLeaves
    (P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ))
    (fun _ : ℕ => (1 : ℝ))
    s.selectedPrefix s.positive s.mass s.remaining

theorem raw_signed_highQ_eq_leaf_sum
    (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (s : FirstExitDepthState ℕ) :
    rawSignedHighQ e q om N cap w L X F s =
      ((rawRetainedLeaves e q om N s).map
        (leafHighQTerm N cap w L X F)).sum := by
  unfold rawSignedHighQ
  rw [signedTest_eq_leaves]
  change ((rawRetainedLeaves e q om N s).map
    (fun leaf => leaf.value *
      attachedLeafTest N cap 1 w L (highQTest X F)
        leaf.positive leaf.selected)).sum = _
  apply congrArg List.sum
  apply List.map_congr_left
  intro leaf _
  simp [leafHighQTerm, attachedLeafTest]

theorem licensed_signed_highQ_eq_leaf_sum
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (s : FirstExitDepthState ℕ) :
    licensedSignedHighQ delta n e q om N cap w L X F s =
      ((licensedRetainedLeaves delta n e q om N s).map
        (leafHighQTerm N cap w L X F)).sum := by
  unfold licensedSignedHighQ
  rw [signedTest_eq_leaves]
  change ((licensedRetainedLeaves delta n e q om N s).map
    (fun leaf => leaf.value *
      attachedLeafTest N cap 1 w L (highQTest X F)
        leaf.positive leaf.selected)).sum = _
  apply congrArg List.sum
  apply List.map_congr_left
  intro leaf _
  simp [leafHighQTerm, attachedLeafTest]

private theorem map_sum_zero_of_each_zero {α : Type*}
    (xs : List α) (f : α → ℝ)
    (h : ∀ x ∈ xs, f x = 0) : (xs.map f).sum = 0 := by
  have he : xs.map f = xs.map (fun _ => (0 : ℝ)) := by
    apply List.map_congr_left
    intro x hx
    exact h x hx
  rw [he]
  simp

/-- Only the leaf's OWN sign-dependent nonzero beta is relevant. -/
theorem raw_signed_zero_of_active_cut
    (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (s : FirstExitDepthState ℕ)
    (hcut : ∀ leaf ∈ rawRetainedLeaves e q om N s,
      ∀ a ∈ actualSmallRosserSupport N cap w,
        (if leaf.positive then actualSmallRosserPlus N cap w L a
         else actualSmallRosserMinus N cap w L a) ≠ 0 →
        a * leaf.selected.prod ≤ X) :
    rawSignedHighQ e q om N cap w L X F s = 0 := by
  rw [raw_signed_highQ_eq_leaf_sum]
  apply map_sum_zero_of_each_zero
  intro leaf hleaf
  exact leafHighQTerm_zero_of_active_sign_cut
    N cap w L X F leaf (hcut leaf hleaf)

/-- Licensed leaves are tested separately, without a raw mask. -/
theorem licensed_signed_zero_of_active_cut
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (s : FirstExitDepthState ℕ)
    (hcut : ∀ leaf ∈ licensedRetainedLeaves delta n e q om N s,
      ∀ a ∈ actualSmallRosserSupport N cap w,
        (if leaf.positive then actualSmallRosserPlus N cap w L a
         else actualSmallRosserMinus N cap w L a) ≠ 0 →
        a * leaf.selected.prod ≤ X) :
    licensedSignedHighQ delta n e q om N cap w L X F s = 0 := by
  rw [licensed_signed_highQ_eq_leaf_sum]
  apply map_sum_zero_of_each_zero
  intro leaf hleaf
  exact leafHighQTerm_zero_of_active_sign_cut
    N cap w L X F leaf (hcut leaf hleaf)

/-- A nonzero raw-only term requires a real strict full-q leaf witness. -/
theorem raw_nonzero_has_active_highQ_witness
    (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (s : FirstExitDepthState ℕ)
    (hn : rawSignedHighQ e q om N cap w L X F s ≠ 0) :
    ∃ leaf ∈ rawRetainedLeaves e q om N s,
      ∃ a ∈ actualSmallRosserSupport N cap w,
        (if leaf.positive then actualSmallRosserPlus N cap w L a
         else actualSmallRosserMinus N cap w L a) ≠ 0 ∧
        X < a * leaf.selected.prod := by
  by_contra hnone
  apply hn
  apply raw_signed_zero_of_active_cut e q om N cap w L X F s
  intro leaf hleaf a ha hbeta
  by_contra hle
  exact hnone ⟨leaf, hleaf, a, ha, hbeta, Nat.lt_of_not_ge hle⟩

theorem licensed_nonzero_has_active_highQ_witness
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (s : FirstExitDepthState ℕ)
    (hn : licensedSignedHighQ delta n e q om N cap w L X F s ≠ 0) :
    ∃ leaf ∈ licensedRetainedLeaves delta n e q om N s,
      ∃ a ∈ actualSmallRosserSupport N cap w,
        (if leaf.positive then actualSmallRosserPlus N cap w L a
         else actualSmallRosserMinus N cap w L a) ≠ 0 ∧
        X < a * leaf.selected.prod := by
  by_contra hnone
  apply hn
  apply licensed_signed_zero_of_active_cut
    delta n e q om N cap w L X F s
  intro leaf hleaf a ha hbeta
  by_contra hle
  exact hnone ⟨leaf, hleaf, a, ha, hbeta, Nat.lt_of_not_ge hle⟩

/-- The actual original 87-cell owner/trim RAW and LICENSED state lists. -/
noncomputable def actualCellCopies
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (c : Cell) :
    List (FirstExitDepthState ℕ) ×
      List (FirstExitDepthState ℕ) × List (FirstExitDepthState ℕ) := by
  classical
  exact pairedCopies
    (rawOwnedTrimmed delta e q om N cap w z c)
    (states delta n e q om N cap w z (fun _ : ℕ => (1 : ℝ)) c)

/-- A genuinely signed physical leaf balance, not a numerical archive sum. -/
def actualCellSignedLeafBalance
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) (c : Cell) : ℝ :=
  let copies := actualCellCopies delta n e q om N cap w z c
  ((copies.1).map (fun s =>
    ((actualMatchedExclusiveLeaves delta n e q om N s).map
      (taggedHighQTerm N cap w L X F)).sum)).sum +
  ((copies.2.1).map (fun s =>
    ((rawRetainedLeaves e q om N s).map
      (leafHighQTerm N cap w L X F)).sum)).sum -
  ((copies.2.2).map (fun s =>
    ((licensedRetainedLeaves delta n e q om N s).map
      (leafHighQTerm N cap w L X F)).sum)).sum

/-- Existing real producerLedger.1, not an invented second ledger, is
equal to the three distinct true first-exit physical leaf sums. -/
theorem actual_cell_ledger_eq_signed_leaf_balance
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) (c : Cell) :
    (actualCellLedger delta n e q om N cap w z L X F c).1 =
      actualCellSignedLeafBalance delta n e q om N cap w z L X F c := by
  classical
  unfold actualCellLedger actualCellSignedLeafBalance actualCellCopies
  rw [producerLedger_signed]
  rw [pairedCopies_signed]
  simp_rw [actual_matched_signed_difference_eq_exclusive,
    raw_signed_highQ_eq_leaf_sum, licensed_signed_highQ_eq_leaf_sum]

theorem actual_owned87_ledger_eq_signed_leaf_balance
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) :
    (∑ c : Cell,
      (actualCellLedger delta n e q om N cap w z L X F c).1) =
      ∑ c : Cell,
        actualCellSignedLeafBalance delta n e q om N cap w z L X F c := by
  classical
  apply Finset.sum_congr rfl
  intro c _
  exact actual_cell_ledger_eq_signed_leaf_balance
    delta n e q om N cap w z L X F c

end
end ImbalancedChen.P4AOriginalFull87UnmatchedPhysicalLeaves
