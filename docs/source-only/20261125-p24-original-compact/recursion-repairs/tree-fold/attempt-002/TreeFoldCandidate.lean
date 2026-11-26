import ImbalancedChen.P2OriginalPriorityForestLedger

/-!
Isolated computable fold over the existing source-indexed tree.
This module adds only the shared fold and its equations; it does not replace
the canonical Ledger or claim canonical compilation/audit credit.
-/

namespace ImbalancedChen.P2OriginalPriorityForestLedgerSourceOnly

open P4AOriginalInitialSeedInventorySourceOnly
open P2OriginalAdaptiveSourceSplitSourceOnly
open P2OriginalPrioritySerialQueueSourceOnly

/-- A total fold with an explicit structural fuel argument. -/
def treeFoldFuel {enclose : SeedCell → Bounds} {β : Type*}
    (fallback : β) (leaf : SeedCell → ℕ → β)
    (split : SeedCell → β → β → β) (fuel : ℕ) :
    {c : SeedCell} → SourceTree enclose c → β :=
  Nat.rec (motive := fun _ => {c : SeedCell} → SourceTree enclose c → β)
    (fun {_} _ => fallback)
    (fun _ previous {_} tree =>
      match tree with
      | .leaf c serial => leaf c serial
      | .split c _ left right => split c (previous left) (previous right))
    fuel

/-- A computable bound from the original raw integer cell widths. -/
private def treeDepthBudget (c : SeedCell) : ℕ :=
  (c.2 0 - c.1 0).toNat + (c.2 1 - c.1 1).toNat + (c.2 2 - c.1 2).toNat

private theorem treeDepthBudget_children (c : SeedCell)
    (width : c.1 (originalAxis c) + 2 ≤ c.2 (originalAxis c)) :
    treeDepthBudget (sourceLeft c) < treeDepthBudget c ∧
      treeDepthBudget (sourceRight c) < treeDepthBudget c := by
  have hmid := originalMidpoint_interior c width
  unfold treeDepthBudget sourceLeft sourceRight
  generalize haxis : originalAxis c = axis at hmid ⊢
  fin_cases axis <;> simp at hmid ⊢ <;> omega

private theorem treeFoldFuel_stable {enclose : SeedCell → Bounds} {β : Type*}
    (fallback : β) (leaf : SeedCell → ℕ → β)
    (split : SeedCell → β → β → β) {c : SeedCell}
    (tree : SourceTree enclose c) (n m : ℕ)
    (hn : treeDepthBudget c < n) (hm : treeDepthBudget c < m) :
    treeFoldFuel fallback leaf split n tree =
      treeFoldFuel fallback leaf split m tree := by
  induction tree generalizing n m with
  | leaf c serial =>
      cases n with
      | zero => omega
      | succ n =>
          cases m with
          | zero => omega
          | succ m => rfl
  | split c width left right ihL ihR =>
      obtain ⟨hleft, hright⟩ := treeDepthBudget_children c width
      cases n with
      | zero => omega
      | succ n =>
          cases m with
          | zero => omega
          | succ m =>
              have hnL : treeDepthBudget (sourceLeft c) < n := by omega
              have hnR : treeDepthBudget (sourceRight c) < n := by omega
              have hmL : treeDepthBudget (sourceLeft c) < m := by omega
              have hmR : treeDepthBudget (sourceRight c) < m := by omega
              change split c (treeFoldFuel fallback leaf split n left)
                  (treeFoldFuel fallback leaf split n right) =
                split c (treeFoldFuel fallback leaf split m left)
                  (treeFoldFuel fallback leaf split m right)
              exact congrArg₂ (split c) (ihL n m hnL hmL) (ihR n m hnR hmR)

/-- Original strict-interior cuts decrease the computed cell-width budget. -/
def treeFold {enclose : SeedCell → Bounds} {β : Type*}
    (fallback : β) (leaf : SeedCell → ℕ → β)
    (split : SeedCell → β → β → β) {c : SeedCell}
    (tree : SourceTree enclose c) : β :=
  treeFoldFuel fallback leaf split (treeDepthBudget c + 1) tree

theorem treeFold_leaf {enclose : SeedCell → Bounds} {β : Type*}
    (fallback : β) (leaf : SeedCell → ℕ → β)
    (split : SeedCell → β → β → β) (c : SeedCell) (serial : ℕ) :
    treeFold fallback leaf split (SourceTree.leaf (enclose := enclose) c serial) =
      leaf c serial := by
  rfl

theorem treeFold_split {enclose : SeedCell → Bounds} {β : Type*}
    (fallback : β) (leaf : SeedCell → ℕ → β)
    (split : SeedCell → β → β → β) (c : SeedCell)
    (width : c.1 (originalAxis c) + 2 ≤ c.2 (originalAxis c))
    (left : SourceTree enclose (sourceLeft c))
    (right : SourceTree enclose (sourceRight c)) :
    treeFold fallback leaf split (SourceTree.split c width left right) =
      split c (treeFold fallback leaf split left) (treeFold fallback leaf split right) := by
  obtain ⟨hleft, hright⟩ := treeDepthBudget_children c width
  change split c
      (treeFoldFuel fallback leaf split (treeDepthBudget c) left)
      (treeFoldFuel fallback leaf split (treeDepthBudget c) right) =
    split c (treeFoldFuel fallback leaf split (treeDepthBudget (sourceLeft c) + 1) left)
      (treeFoldFuel fallback leaf split (treeDepthBudget (sourceRight c) + 1) right)
  exact congrArg₂ (split c)
    (treeFoldFuel_stable fallback leaf split left _ _ hleft (by omega))
    (treeFoldFuel_stable fallback leaf split right _ _ hright (by omega))

end ImbalancedChen.P2OriginalPriorityForestLedgerSourceOnly
