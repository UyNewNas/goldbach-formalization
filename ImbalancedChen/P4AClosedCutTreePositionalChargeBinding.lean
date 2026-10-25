import ImbalancedChen.P4AOriginalClosedTreeStructuralAggregation
import Mathlib.Data.List.Forall2

/-!
SOURCEONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The existing tree recursor and positional aggregation are already installed.
This module constructs a shape-preserving annotation from an exactly sized
integer list, and proves that its recursive local bound is precisely the
positional List.Forall₂ bound on the original closedLeaves list. It neither
reorders charges nor discards empty or zero-width leaves.

OPEN: the original adaptive ClosedCutTree, its complete charge list, each
actual leaf bound, and the historical integer-sum bound are still absent.
An aggregate digest is not an input to this construction.
-/

namespace ImbalancedChen.P4AClosedCutTreePositionalChargeBindingSourceOnly

noncomputable section
open Set MeasureTheory
open OriginalThirdCompactPartitionSourceOnly
open P4AOriginalClosedTreeStructuralAggregationSourceOnly

/-- Charges in exactly the left-to-right order of the closed leaf recursor. -/
def leafCharges : ChargedCutTree → List ℤ
  | .leaf q => [q]
  | .split _ _ left right => leafCharges left ++ leafCharges right

theorem leafCharges_length (tree : ChargedCutTree) (s : Set Point) :
    (leafCharges tree).length = (closedLeaves (eraseCharges tree) s).length := by
  induction tree generalizing s with
  | leaf q => rfl
  | split axis cut left right ihL ihR =>
      simp only [leafCharges, eraseCharges, closedLeaves, List.length_append]
      rw [ihL (s ∩ {t : Point | t axis ≤ (cut : ℝ) / coordinateDenominator}),
        ihR (s ∩ {t : Point | (cut : ℝ) / coordinateDenominator ≤ t axis})]

theorem totalCharge_eq_leafCharges_sum (tree : ChargedCutTree) :
    totalCharge tree = (leafCharges tree).sum := by
  induction tree with
  | leaf q => simp [totalCharge, leafCharges]
  | split axis cut left right ihL ihR =>
      simp only [totalCharge, leafCharges, List.sum_append, ihL, ihR]

/-- This constructor consumes every supplied charge exactly once. The length
guard is structural, before any local analytic bound is considered. -/
def attachCharges (tree : ClosedCutTree) (charges : List ℤ)
    (hsize : charges.length = splitCount tree + 1) :
    {annotated : ChargedCutTree //
      eraseCharges annotated = tree ∧ leafCharges annotated = charges} := by
  induction tree generalizing charges with
  | leaf =>
      cases charges with
      | nil => simp [splitCount] at hsize
      | cons q rest =>
          have hrest : rest = [] := by
            apply List.length_eq_zero_iff.mp
            simp only [List.length_cons, splitCount] at hsize
            omega
          subst rest
          exact ⟨.leaf q, rfl, rfl⟩
  | split axis cut left right ihL ihR =>
      let n := splitCount left + 1
      have htotal : charges.length = n + (splitCount right + 1) := by
        simp only [splitCount] at hsize
        dsimp [n]
        omega
      have htake : (charges.take n).length = splitCount left + 1 := by
        rw [List.length_take, Nat.min_eq_left (by omega : n ≤ charges.length)]
      have hdrop : (charges.drop n).length = splitCount right + 1 := by
        rw [List.length_drop]
        omega
      obtain ⟨left', hleftErase, hleftCharges⟩ := ihL (charges.take n) htake
      obtain ⟨right', hrightErase, hrightCharges⟩ := ihR (charges.drop n) hdrop
      refine ⟨.split axis cut left' right', ?_, ?_⟩
      · simp only [eraseCharges, hleftErase, hrightErase]
      · simp only [leafCharges, hleftCharges, hrightCharges]
        exact List.take_append_drop n charges

/-- The constructor's first projection keeps the actual split data. -/
theorem attachCharges_erase (tree : ClosedCutTree) (charges : List ℤ)
    (hsize : charges.length = splitCount tree + 1) :
    eraseCharges (attachCharges tree charges hsize).val = tree :=
  (attachCharges tree charges hsize).property.1

/-- The constructor's second projection keeps the complete positional list. -/
theorem attachCharges_list (tree : ClosedCutTree) (charges : List ℤ)
    (hsize : charges.length = splitCount tree + 1) :
    leafCharges (attachCharges tree charges hsize).val = charges :=
  (attachCharges tree charges hsize).property.2

private theorem forall₂_append_iff_of_length_eq
    {α β : Type*} {R : α → β → Prop}
    (xs ys : List α) (us vs : List β) (hlen : xs.length = us.length) :
    List.Forall₂ R (xs ++ ys) (us ++ vs) ↔
      List.Forall₂ R xs us ∧ List.Forall₂ R ys vs := by
  induction xs generalizing us with
  | nil =>
      have hu : us = [] := List.length_eq_zero_iff.mp hlen.symm
      subst us
      simp
  | cons x xs ih =>
      cases us with
      | nil => simp at hlen
      | cons u us =>
          have hlen' : xs.length = us.length := Nat.succ.inj hlen
          simp only [List.cons_append, List.forall₂_cons]
          rw [ih us hlen']
          tauto

/-- Recursive local bounds and positional local bounds are the same assertion
on an annotated tree; the append split is justified by exact child lengths. -/
theorem localChargeBound_iff_positional (tree : ChargedCutTree) :
    ∀ s : Set Point,
      LocalChargeBound tree s ↔
        List.Forall₂ (fun c q =>
          (∫ t in c, compactKernel t) ≤ (q : ℝ) / 2^80)
          (closedLeaves (eraseCharges tree) s) (leafCharges tree) := by
  induction tree with
  | leaf q =>
      intro s
      simp [LocalChargeBound, eraseCharges, closedLeaves, leafCharges]
  | split axis cut left right ihL ihR =>
      intro s
      let sL := s ∩ {t : Point | t axis ≤ (cut : ℝ) / coordinateDenominator}
      let sR := s ∩ {t : Point | (cut : ℝ) / coordinateDenominator ≤ t axis}
      change (LocalChargeBound left sL ∧ LocalChargeBound right sR) ↔
        List.Forall₂ _
          (closedLeaves (eraseCharges left) sL ++
            closedLeaves (eraseCharges right) sR)
          (leafCharges left ++ leafCharges right)
      rw [forall₂_append_iff_of_length_eq _ _ _ _
        (leafCharges_length left sL).symm]
      exact and_congr (ihL sL) (ihR sR)

/-- Concrete tree and charge data may use the structural constructor directly;
the only remaining analytic input is the original leaf-by-leaf relation. -/
theorem attachCharges_local_iff (tree : ClosedCutTree) (charges : List ℤ)
    (hsize : charges.length = splitCount tree + 1) (s : Set Point) :
    LocalChargeBound (attachCharges tree charges hsize).val s ↔
      List.Forall₂ (fun c q =>
        (∫ t in c, compactKernel t) ≤ (q : ℝ) / 2^80)
        (closedLeaves tree s) charges := by
  rw [localChargeBound_iff_positional, attachCharges_erase, attachCharges_list]

end
end ImbalancedChen.P4AClosedCutTreePositionalChargeBindingSourceOnly
