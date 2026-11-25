import ImbalancedChen.Data.P1HistoricalFifthSavedTableData
import ImbalancedChen.P1FifthGrid400UnitBoxPartition
import Mathlib

namespace ImbalancedChen.P1HistoricalFifthTypedKeyPartition
open P1OriginalPrefixRowDecodeSoundness P1FifthGrid400UnitBoxPartition

/-- A function of the FIVE original geometry keys only. No converse code
injectivity premise is needed: equal geometry keys necessarily give equal
codes. The closed decision below concerns the full independent source list. -/
def codeOfKey (key : Fin 5 → ℤ) : ℕ :=
  ((((key 0).toNat * 400 + (key 1).toNat) * 400 + (key 2).toNat) * 400 +
    (key 3).toNat) * 400 + (key 4).toNat

def typedCodes : List ℕ :=
  Data.P1HistoricalFifthSavedTableData.rows.toList.map (fun raw => codeOfKey (rowKey raw))

def sortedCodes : List ℕ := typedCodes.mergeSort (fun a b => decide (a ≤ b))

/-- Linear adjacent comparisons after mergeSort; unlike a direct Nodup
decision on the unsorted list, this does not compare every pair of rows. -/
def AdjacentStrict : List ℕ → Prop
  | [] => True
  | [_] => True
  | a :: b :: tail => a < b ∧ AdjacentStrict (b :: tail)

instance adjacentStrictDecidable (xs : List ℕ) : Decidable (AdjacentStrict xs) := by
  induction xs with
  | nil => exact isTrue trivial
  | cons a xs ih =>
    cases xs with
    | nil => exact isTrue trivial
    | cons b tail =>
      change Decidable (a < b ∧ AdjacentStrict (b :: tail))
      letI : Decidable (AdjacentStrict (b :: tail)) := ih
      infer_instance

theorem adjacentStrict_tail (a : ℕ) (xs : List ℕ) (h : AdjacentStrict (a :: xs)) :
    AdjacentStrict xs := by
  cases xs with
  | nil => trivial
  | cons b tail => exact h.2

theorem adjacentStrict_head_lt (a : ℕ) (xs : List ℕ) (h : AdjacentStrict (a :: xs)) :
    ∀ b ∈ xs, a < b := by
  induction xs generalizing a with
  | nil => simp
  | cons b xs ih =>
    intro c hc
    rcases List.mem_cons.mp hc with heq | hc
    · subst c
      exact h.1
    · exact lt_trans h.1 (ih b h.2 c hc)

theorem adjacentStrict_nodup (xs : List ℕ) (h : AdjacentStrict xs) : xs.Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons a xs ih =>
    apply List.nodup_cons.mpr
    refine ⟨?_, ih (adjacentStrict_tail a xs h)⟩
    intro ha
    exact (lt_irrefl a) (adjacentStrict_head_lt a xs h a ha)

end ImbalancedChen.P1HistoricalFifthTypedKeyPartition
