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

private theorem treeFoldFuel_stable {enclose : SeedCell → Bounds} {β : Type*}
    (fallback : β) (leaf : SeedCell → ℕ → β)
    (split : SeedCell → β → β → β) {c : SeedCell}
    (tree : SourceTree enclose c) (n m : ℕ)
    (hn : sizeOf tree < n) (hm : sizeOf tree < m) :
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
      cases n with
      | zero => omega
      | succ n =>
          cases m with
          | zero => omega
          | succ m =>
              have hnL : sizeOf left < n := by
                simp only [SourceTree.split.sizeOf_spec] at hn
                omega
              have hnR : sizeOf right < n := by
                simp only [SourceTree.split.sizeOf_spec] at hn
                omega
              have hmL : sizeOf left < m := by
                simp only [SourceTree.split.sizeOf_spec] at hm
                omega
              have hmR : sizeOf right < m := by
                simp only [SourceTree.split.sizeOf_spec] at hm
                omega
              change split c (treeFoldFuel fallback leaf split n left)
                  (treeFoldFuel fallback leaf split n right) =
                split c (treeFoldFuel fallback leaf split m left)
                  (treeFoldFuel fallback leaf split m right)
              exact congrArg₂ (split c) (ihL n m hnL hmL) (ihR n m hnR hmR)

/-- The size bound is sufficient for every branch; it is not a node count. -/
def treeFold {enclose : SeedCell → Bounds} {β : Type*}
    (fallback : β) (leaf : SeedCell → ℕ → β)
    (split : SeedCell → β → β → β) {c : SeedCell}
    (tree : SourceTree enclose c) : β :=
  treeFoldFuel fallback leaf split (sizeOf tree + 1) tree

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
  have hleft : sizeOf left < sizeOf (SourceTree.split c width left right) := by
    simp only [SourceTree.split.sizeOf_spec]
    omega
  have hright : sizeOf right < sizeOf (SourceTree.split c width left right) := by
    simp only [SourceTree.split.sizeOf_spec]
    omega
  change split c
      (treeFoldFuel fallback leaf split (sizeOf (SourceTree.split c width left right)) left)
      (treeFoldFuel fallback leaf split (sizeOf (SourceTree.split c width left right)) right) =
    split c (treeFoldFuel fallback leaf split (sizeOf left + 1) left)
      (treeFoldFuel fallback leaf split (sizeOf right + 1) right)
  exact congrArg₂ (split c)
    (treeFoldFuel_stable fallback leaf split left _ _ hleft (by omega))
    (treeFoldFuel_stable fallback leaf split right _ _ hright (by omega))

end ImbalancedChen.P2OriginalPriorityForestLedgerSourceOnly
