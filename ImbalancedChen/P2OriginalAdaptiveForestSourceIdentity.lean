import ImbalancedChen.P2OriginalInitialClosedTree
import ImbalancedChen.P4AClosedCutTreePositionalChargeBinding

/-!
SOURCEONLY / UNCOMPILED / BROAD P2.4 OPEN.

The original producer starts its 21 adaptive subtrees at `initialSeeds`,
whose x/y lower endpoints are z0. The skeleton's unnormalised integer boxes
are not those raw producer boxes. This file proves that grafting those
subtrees into the original skeleton gives exactly the raw producer forest's
ordered leaf domains, with no per-leaf set-equality premise. In particular,
normalisation occurs BEFORE the producer chooses later relative-width cuts.

No historical adaptive subtree, enclosure charge, analytic leaf payment, or
2M-step endpoint is invented or assumed here. The original output did not
serialize its adaptive tree or its leaf charges.
-/

namespace ImbalancedChen.P2OriginalAdaptiveForestSourceIdentitySourceOnly

noncomputable section
open Set MeasureTheory
open OriginalThirdCompactPartitionSourceOnly
open P4AOriginalClosedTreeStructuralAggregationSourceOnly
open P4AClosedCutTreePositionalChargeBindingSourceOnly
open P4AClosedTreeCoordinatePropagationSourceOnly
open P4AOriginalInitialSeedInventorySourceOnly
open P2OriginalInitialClosedTreeSourceOnly

/-- Traverse each supplied subtree on its corresponding domain, keeping all
leaves. Length agreement is enforced by the graft constructor below. -/
def forestLeaves : List ClosedCutTree → List (Set Point) → List (Set Point)
  | tree :: trees, s :: sets => closedLeaves tree s ++ forestLeaves trees sets
  | _, _ => []

private theorem forestLeaves_append (left right : List ClosedCutTree)
    (xs ys : List (Set Point)) (hlen : left.length = xs.length) :
    forestLeaves (left ++ right) (xs ++ ys) =
      forestLeaves left xs ++ forestLeaves right ys := by
  induction left generalizing xs with
  | nil =>
      have hx : xs = [] := List.length_eq_zero_iff.mp hlen.symm
      subst xs
      rfl
  | cons tree trees ih =>
      cases xs with
      | nil => simp at hlen
      | cons s sets =>
          have htail : trees.length = sets.length := Nat.succ.inj hlen
          simpa only [List.cons_append, forestLeaves, List.append_assoc] using
            congrArg (fun tail => closedLeaves tree s ++ tail) (ih sets htail)

/-- Substitute one actual adaptive subtree at every skeleton leaf. All
supplied trees are consumed once, in the skeleton's original leaf order. -/
def graftSubtrees (skeleton : ClosedCutTree) (trees : List ClosedCutTree)
    (hsize : trees.length = splitCount skeleton + 1) :
    {refined : ClosedCutTree //
      ∀ s, closedLeaves refined s = forestLeaves trees (closedLeaves skeleton s)} := by
  induction skeleton generalizing trees with
  | leaf =>
      cases trees with
      | nil => simp [splitCount] at hsize
      | cons tree rest =>
          have hrest : rest = [] := by
            apply List.length_eq_zero_iff.mp
            simp only [List.length_cons, splitCount] at hsize
            omega
          subst rest
          exact ⟨tree, fun s => by simp [forestLeaves,closedLeaves]⟩
  | split axis cut left right ihL ihR =>
      let n := splitCount left + 1
      have htotal : trees.length = n + (splitCount right + 1) := by
        simp only [splitCount] at hsize
        dsimp [n]
        omega
      have htake : (trees.take n).length = splitCount left + 1 := by
        rw [List.length_take, Nat.min_eq_left (by omega : n ≤ trees.length)]
      have hdrop : (trees.drop n).length = splitCount right + 1 := by
        rw [List.length_drop]
        omega
      obtain ⟨left',hleft⟩ := ihL (trees.take n) htake
      obtain ⟨right',hright⟩ := ihR (trees.drop n) hdrop
      refine ⟨.split axis cut left' right', ?_⟩
      intro s
      let sL := s ∩ {t : Point | t axis ≤ (cut : ℝ) / coordinateDenominator}
      let sR := s ∩ {t : Point | (cut : ℝ) / coordinateDenominator ≤ t axis}
      change closedLeaves left' sL ++ closedLeaves right' sR =
        forestLeaves trees (closedLeaves left sL ++ closedLeaves right sR)
      rw [hleft,hright]
      have hlen : (trees.take n).length = (closedLeaves left sL).length := by
        rw [htake,closedLeaves_length]
      conv_rhs => rw [← List.take_append_drop n trees]
      rw [forestLeaves_append _ _ _ _ hlen]

/-- Raw integer boxes produced by the adaptive subtree at each ORIGINAL
seed. This uses the raised z0 lower endpoints in the source inventory. -/
def sourceIntegerForest : List ClosedCutTree → List SeedCell → List SeedCell
  | tree :: trees, c :: cells =>
      integerLeafBoxes tree c.1 c.2 ++ sourceIntegerForest trees cells
  | _, _ => []

/-- This is an exact ordered list identity, including empty source portions
and both copies of closed split faces. No source cover is supplied as input. -/
theorem forestLeaves_eq_source_integer_domains
    (trees : List ClosedCutTree) (cells : List SeedCell) :
    forestLeaves trees (cells.map rootCell) =
      (sourceIntegerForest trees cells).map rootCell := by
  induction trees generalizing cells with
  | nil => simp [forestLeaves,sourceIntegerForest]
  | cons tree trees ih =>
      cases cells with
      | nil => simp [forestLeaves,sourceIntegerForest]
      | cons c cells =>
          simp only [List.map_cons,forestLeaves,sourceIntegerForest,List.map_append]
          rw [ih]
          congr 1
          exact compact_closedLeaves_eq_integer_boxes tree c.1 c.2

private theorem initialTree_splitCount : splitCount initialTree + 1 = 21 := by
  have h := closedLeaves_initialTree_length
  rw [closedLeaves_length] at h
  exact h

/-- A fully specified constructor at the actual original 21-seed skeleton.
The argument is the future immutable list of adaptive subtrees, not a
numerical enclosure or a hypothesis of the desired compact estimate. -/
def originalAdaptiveTree (trees : List ClosedCutTree) (hsize : trees.length = 21) :
    ClosedCutTree :=
  (graftSubtrees initialTree trees (hsize.trans initialTree_splitCount.symm)).val

/-- The missing source-to-tree dictionary for arbitrary adaptive descendants
of all 21 actual raw seeds. This prevents choosing later axes from the
skeleton's unnormalised boxes and preserves original x-outer/y-inner order. -/
theorem originalAdaptiveTree_closedLeaves (trees : List ClosedCutTree)
    (hsize : trees.length = 21) :
    closedLeaves (originalAdaptiveTree trees hsize) compactRegion =
      (sourceIntegerForest trees initialSeeds).map rootCell := by
  unfold originalAdaptiveTree
  rw [(graftSubtrees initialTree trees
      (hsize.trans initialTree_splitCount.symm)).property,
    closedLeaves_initialTree_eq_original_seedCells,
    forestLeaves_eq_source_integer_domains]

/-- Exact equality with the ORIGINAL compact correction; this theorem has no
charge premise, positivity premise or analytic enclosure premise. -/
theorem originalCompact_eq_source_integer_forest (trees : List ClosedCutTree)
    (hsize : trees.length = 21) :
    originalCompactThirdCorrection =
      (((sourceIntegerForest trees initialSeeds).map rootCell).map
        (fun c => ∫ t in c, compactKernel t)).sum := by
  rw [originalCompactThirdCorrection_eq_sum_closedLeaves
      (originalAdaptiveTree trees hsize),originalAdaptiveTree_closedLeaves]

/-- The existing positional binder can now consume the raw producer forest
with a proved leaf identity, instead of an assumed family/domain alignment. -/
theorem originalAdaptiveTree_charge_binding (trees : List ClosedCutTree)
    (htrees : trees.length = 21) (charges : List ℤ)
    (hcharges : charges.length = splitCount (originalAdaptiveTree trees htrees) + 1) :
    LocalChargeBound
        (attachCharges (originalAdaptiveTree trees htrees) charges hcharges).val
        compactRegion ↔
      List.Forall₂ (fun c q =>
        (∫ t in c, compactKernel t) ≤ (q : ℝ) / 2^80)
        ((sourceIntegerForest trees initialSeeds).map rootCell) charges := by
  rw [attachCharges_local_iff,originalAdaptiveTree_closedLeaves]

/-- In particular, the COMPLETE charge list is indexed by the complete raw
forest, not by the positive-width heap. Exact leaves cannot be omitted. -/
theorem sourceIntegerForest_charge_length (trees : List ClosedCutTree)
    (htrees : trees.length = 21) (charges : List ℤ)
    (hcharges : charges.length = splitCount (originalAdaptiveTree trees htrees) + 1) :
    charges.length = (sourceIntegerForest trees initialSeeds).length := by
  have hlen := closedLeaves_length (originalAdaptiveTree trees htrees) compactRegion
  rw [originalAdaptiveTree_closedLeaves,List.length_map] at hlen
  exact hcharges.trans hlen.symm

private theorem integerLeafBoxes_length (tree : ClosedCutTree)
    (a b : Fin 3 → ℤ) :
    (integerLeafBoxes tree a b).length = splitCount tree + 1 := by
  have h := congrArg List.length (compact_closedLeaves_eq_integer_boxes tree a b)
  simp only [List.length_map,closedLeaves_length] at h
  exact h.symm

/-- The complete raw forest has one more leaf for EVERY adaptive split;
the heap's filter on positive enclosure width is not present in this count. -/
theorem sourceIntegerForest_length (trees : List ClosedCutTree) (cells : List SeedCell)
    (hsize : trees.length = cells.length) :
    (sourceIntegerForest trees cells).length =
      (trees.map splitCount).sum + trees.length := by
  induction trees generalizing cells with
  | nil => simp [sourceIntegerForest]
  | cons tree trees ih =>
      cases cells with
      | nil => simp at hsize
      | cons c cells =>
          have htail : trees.length = cells.length := Nat.succ.inj hsize
          simp only [sourceIntegerForest,List.length_append,integerLeafBoxes_length,
            List.map_cons,List.sum_cons,List.length_cons]
          rw [ih cells htail]
          omega

/-- If the frozen two-million split history is later supplied, its complete
source leaf inventory must contain 2,000,021 entries. This does not assert
that the missing history is supplied, or identify heap entries with leaves. -/
theorem frozen_original_full_leaf_count (trees : List ClosedCutTree)
    (htrees : trees.length = 21)
    (hsplits : (trees.map splitCount).sum = 2000000) :
    (sourceIntegerForest trees initialSeeds).length = 2000021 := by
  have hsize : trees.length = initialSeeds.length := by
    rw [initialSeeds_eq_records,records_length]
    exact htrees
  rw [sourceIntegerForest_length trees initialSeeds hsize,hsplits,htrees]

end
end ImbalancedChen.P2OriginalAdaptiveForestSourceIdentitySourceOnly
