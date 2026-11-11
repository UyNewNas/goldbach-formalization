import ImbalancedChen.P4AOriginalFull87EighthPrimeMeanLedger
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

An actual finite PP call-site adapter for the original 87 owned rank-eight
occurrence lists. The primitive-error saving is expanded into leaves of
the ORIGINAL ordinary policies, with the ORIGINAL small sign-dependent
Rosser beta and COMPLETE modulus a * leaf.selected.prod.

The resulting absolute budget is localized to the changed owned states.
Unlike the previous global absolutePhysical budget, it never charges
untouched sixth-policy branches. No primitive discrepancy bound, PNT,
external PP estimate, saved numerical gain, or H_N payment is asserted.
-/

namespace ImbalancedChen.P4AOriginalFull87OwnedPrimitiveLedger
noncomputable section
open scoped Classical BigOperators
open P1Pair12RetainedSignedSource (signedTest_eq_leaves attachedLeafTest)
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87SourceDispatch (point8)
open P4AOriginalFull87FiniteEighthCap (finiteCap)
open P4AOriginalFull87EighthKernelIntegration (actualParent)
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87LicensedSixthRealization (states)
open P4AOriginalFull87OwnedEighthSource (ordinarySaving ownedSource)
open P4AOriginalFull87EighthPrimeMeanLedger
  (primitiveError gain gain_eq_owned_sources)

/-- One actual retained leaf, with its own sign-selected small beta.
The modulus is the FULL product, not merely the rough leaf modulus. -/
def primitiveLeaf (N cap : ℕ) (w L : ℝ)
    (leaf : FirstExitLeaf ℕ) : ℝ :=
  leaf.value * ∑ a ∈ actualSmallRosserSupport N cap w,
    (if leaf.positive then actualSmallRosserPlus N cap w L a
     else actualSmallRosserMinus N cap w L a) *
      primitiveError N (a * leaf.selected.prod)

/-- A termwise absolute PP bill for the SAME leaf. -/
def primitiveLeafAbs (N cap : ℕ) (w L : ℝ)
    (leaf : FirstExitLeaf ℕ) : ℝ :=
  |leaf.value| * ∑ a ∈ actualSmallRosserSupport N cap w,
    |if leaf.positive then actualSmallRosserPlus N cap w L a
      else actualSmallRosserMinus N cap w L a| *
      |primitiveError N (a * leaf.selected.prod)|

/-- Old ordinary continuation: the actual frozen sixth ancestor. -/
def beforeLeaves (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N : ℕ) (s : FirstExitDepthState ℕ) : List (FirstExitLeaf ℕ) :=
  firstExitRetainedLeaves
    (ordinaryParityRosserPolicy false
      ((N : ℝ) ^ actualParent n e q om (N : ℝ) s.selectedPrefix))
    (fun _ => 1) s.selectedPrefix s.positive s.mass s.remaining

/-- New ordinary continuation: the original finite eighth cap of its
original owner; this is not an independently selected comparison parent. -/
def afterLeaves (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N : ℕ) (c : Cell) (s : FirstExitDepthState ℕ) :
    List (FirstExitLeaf ℕ) :=
  firstExitRetainedLeaves
    (ordinaryParityRosserPolicy false
      ((N : ℝ) ^ (finiteCap n c (point8 (N : ℝ) s.selectedPrefix) : ℝ)))
    (fun _ => 1) s.selectedPrefix s.positive s.mass s.remaining

/-- Signed local primitive discrepancy saving, with ALL leaf occurrences. -/
def primitiveStateSaving (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w L : ℝ) (c : Cell)
    (s : FirstExitDepthState ℕ) : ℝ :=
  ((beforeLeaves n e q om N s).map (primitiveLeaf N cap w L)).sum -
  ((afterLeaves n e q om N c s).map (primitiveLeaf N cap w L)).sum

/-- Absolute primitive discrepancy bill for exactly the two continuations
of this owned state, not for the entire unaffected physical source. -/
def primitiveStateBudget (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w L : ℝ) (c : Cell)
    (s : FirstExitDepthState ℕ) : ℝ :=
  ((beforeLeaves n e q om N s).map (primitiveLeafAbs N cap w L)).sum +
  ((afterLeaves n e q om N c s).map (primitiveLeafAbs N cap w L)).sum

/-- The existing signedTest-to-leaves identity, now at the actual levels,
plus literal beta expansion. No new PP source is postulated. -/
theorem ordinarySaving_primitive_eq_leaf_invoice
    (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w L : ℝ) (c : Cell)
    (s : FirstExitDepthState ℕ) :
    ordinarySaving n e q om N cap w L (primitiveError N) c s =
      primitiveStateSaving n e q om N cap w L c s := by
  simp only [ordinarySaving, primitiveStateSaving, beforeLeaves, afterLeaves,
    signedTest_eq_leaves, primitiveLeaf, attachedLeafTest, one_mul]

/-- The exact per-leaf absolute beta/error budget. -/
theorem abs_primitiveLeaf_le (N cap : ℕ) (w L : ℝ)
    (leaf : FirstExitLeaf ℕ) :
    |primitiveLeaf N cap w L leaf| ≤ primitiveLeafAbs N cap w L leaf := by
  unfold primitiveLeaf primitiveLeafAbs
  rw [abs_mul]
  apply mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  calc
    |∑ a ∈ actualSmallRosserSupport N cap w,
        (if leaf.positive then actualSmallRosserPlus N cap w L a
         else actualSmallRosserMinus N cap w L a) *
          primitiveError N (a * leaf.selected.prod)| ≤
      ∑ a ∈ actualSmallRosserSupport N cap w,
        |(if leaf.positive then actualSmallRosserPlus N cap w L a
          else actualSmallRosserMinus N cap w L a) *
            primitiveError N (a * leaf.selected.prod)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [abs_mul]

/-- List, not Finset: duplicate physical occurrences remain distinct. -/
private theorem abs_list_map_sum_le {α : Type*}
    (xs : List α) (f b : α → ℝ)
    (h : ∀ x ∈ xs, |f x| ≤ b x) :
    |(xs.map f).sum| ≤ (xs.map b).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx : |f x| ≤ b x := h x (by simp)
    have ht : ∀ y ∈ xs, |f y| ≤ b y := by
      intro y hy
      exact h y (List.mem_cons_of_mem x hy)
    simpa only [List.map_cons, List.sum_cons] using
      (abs_add (f x) ((xs.map f).sum)).trans
        (add_le_add hx (ih ht))

theorem abs_primitiveStateSaving_le
    (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w L : ℝ) (c : Cell)
    (s : FirstExitDepthState ℕ) :
    |primitiveStateSaving n e q om N cap w L c s| ≤
      primitiveStateBudget n e q om N cap w L c s := by
  have hbefore := abs_list_map_sum_le
    (beforeLeaves n e q om N s)
    (primitiveLeaf N cap w L) (primitiveLeafAbs N cap w L)
    (fun leaf _ => abs_primitiveLeaf_le N cap w L leaf)
  have hafter := abs_list_map_sum_le
    (afterLeaves n e q om N c s)
    (primitiveLeaf N cap w L) (primitiveLeafAbs N cap w L)
    (fun leaf _ => abs_primitiveLeaf_le N cap w L leaf)
  unfold primitiveStateSaving primitiveStateBudget
  have htriangle :
      |((beforeLeaves n e q om N s).map (primitiveLeaf N cap w L)).sum -
        ((afterLeaves n e q om N c s).map (primitiveLeaf N cap w L)).sum| ≤
      |((beforeLeaves n e q om N s).map (primitiveLeaf N cap w L)).sum| +
        |((afterLeaves n e q om N c s).map (primitiveLeaf N cap w L)).sum| := by
    simpa only [sub_eq_add_neg, abs_neg] using
      abs_add
        ((beforeLeaves n e q om N s).map (primitiveLeaf N cap w L)).sum
        (-((afterLeaves n e q om N c s).map (primitiveLeaf N cap w L)).sum)
  exact htriangle.trans (add_le_add hbefore hafter)

/-- Only the genuine filtered sixth owner/trim state list is charged.
No state is deduplicated, and no unowned branch receives a bill. -/
def ownedPrimitiveBudget (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (c : Cell) : ℝ :=
  ((states (width r) n e q om N cap w z (fun _ => 1) c).map
    (primitiveStateBudget n e q om N cap w L c)).sum

theorem owned_primitive_exact
    (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (c : Cell) :
    ownedSource (width r) n e q om N cap w z L (primitiveError N) c =
      ((states (width r) n e q om N cap w z (fun _ => 1) c).map
        (primitiveStateSaving n e q om N cap w L c)).sum := by
  unfold ownedSource
  apply congrArg List.sum
  apply List.map_congr_left
  intro s hs
  exact ordinarySaving_primitive_eq_leaf_invoice n e q om N cap w L c s

theorem owned_primitive_abs_budget
    (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (c : Cell) :
    |ownedSource (width r) n e q om N cap w z L (primitiveError N) c| ≤
      ownedPrimitiveBudget r n e q om N cap w z L c := by
  rw [owned_primitive_exact]
  unfold ownedPrimitiveBudget
  exact abs_list_map_sum_le
    (states (width r) n e q om N cap w z (fun _ => 1) c)
    (primitiveStateSaving n e q om N cap w L c)
    (primitiveStateBudget n e q om N cap w L c)
    (fun s hs => abs_primitiveStateSaving_le n e q om N cap w L c s)

/-- Actual full87 PRIMITIVE discrepancy saving: a localized arithmetic bill
on the ORIGINAL signed state/leaf/multiplier populations, not the much
larger global old-plus-new absolutePhysical support. This is an exact finite
inequality; controlling its RHS by PP / H_N remains completely OPEN. -/
theorem full87_primitive_owned_budget
    (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) :
    |gain (width r) n e q om N cap w z L (primitiveError N)| ≤
      ∑ c : Cell, ownedPrimitiveBudget r n e q om N cap w z L c := by
  rw [gain_eq_owned_sources]
  calc
    |∑ c : Cell,
      ownedSource (width r) n e q om N cap w z L (primitiveError N) c| ≤
        ∑ c : Cell,
          |ownedSource (width r) n e q om N cap w z L (primitiveError N) c| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ c : Cell, ownedPrimitiveBudget r n e q om N cap w z L c :=
      Finset.sum_le_sum (fun c _ =>
        owned_primitive_abs_budget r n e q om N cap w z L c)

end
end ImbalancedChen.P4AOriginalFull87OwnedPrimitiveLedger
