import ImbalancedChen.Certificates.OriginalNodeArraysV1.All40CheckedTable
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Init.Data.Array.Extract

/-!
SOURCEONLY / UNCOMPILED / NOT PASS / OPEN30.
The first import is the proposed installation name of y-All40 V2. This file
does not recreate its table, replay integer checks, or certify external bytes.
It supplies missing ordered, multiplicity-preserving batch semantics.
-/

namespace P0All40ListFold

open ImbalancedChen
open ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly
open ImbalancedChen.OriginalU2CoupledRecurrenceSourceOnly
open ImbalancedChen.OriginalU2StoredNodeBlockCheckerSourceOnly
open ImbalancedChen.OriginalU2StoredQueryLookupSourceOnly

/-- A List batch retains repeated requests; it is not a Finset sum. -/
def listSum {α β : Type*} [AddMonoid β] (value : α → β) (xs : List α) : β :=
  (xs.map value).sum

theorem listSum_foldl {α β : Type*} [AddMonoid β] (value : α → β)
    (xs : List α) (start : β) :
    xs.foldl (fun acc x => acc + value x) start = start + listSum value xs := by
  induction xs generalizing start with
  | nil => simp [listSum]
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih]
      simp [listSum, add_assoc]

theorem listSum_append {α β : Type*} [AddMonoid β] (value : α → β)
    (xs ys : List α) :
    listSum value (xs ++ ys) = listSum value xs + listSum value ys := by
  simp [listSum, List.map_append, List.sum_append]

/-- Works even when the requested split lies past the end. -/
theorem listSum_split {α β : Type*} [AddMonoid β] (value : α → β)
    (xs : List α) (n : Nat) :
    listSum value xs = listSum value (xs.take n) + listSum value (xs.drop n) := by
  have h := listSum_append value (xs.take n) (xs.drop n)
  rw [List.take_append_drop] at h
  exact h

theorem listSum_congr {α β : Type*} [AddMonoid β] (f g : α → β)
    (xs : List α) (h : ∀ x ∈ xs, f x = g x) :
    listSum f xs = listSum g xs := by
  induction xs with
  | nil => simp [listSum]
  | cons x xs ih =>
      have hx := h x (by simp)
      have ht : listSum f xs = listSum g xs :=
        ih (fun y hy => h y (by simp [hy]))
      change f x + listSum f xs = g x + listSum g xs
      rw [hx, ht]

theorem listSum_mono {α : Type*} (f g : α → Real) (xs : List α)
    (h : ∀ x ∈ xs, f x ≤ g x) : listSum f xs ≤ listSum g xs := by
  induction xs with
  | nil => simp [listSum]
  | cons x xs ih =>
      have hx := h x (by simp)
      have ht : listSum f xs ≤ listSum g xs :=
        ih (fun y hy => h y (by simp [hy]))
      change f x + listSum f xs ≤ g x + listSum g xs
      exact add_le_add hx ht

/-- A common scale may be applied after the exact integer accumulation. -/
theorem listSum_int_cast_div {α : Type*} (value : α → Int) (xs : List α)
    (scale : Real) :
    (listSum value xs : Real) / scale =
      listSum (fun x => (value x : Real) / scale) xs := by
  induction xs with
  | nil => simp [listSum]
  | cons x xs ih =>
      change ((value x + listSum value xs : Int) : Real) / scale =
        (value x : Real) / scale +
          listSum (fun x => (value x : Real) / scale) xs
      rw [Int.cast_add, add_div, ih]

/-- The implementation-facing Array aggregation uses Array.foldl directly. -/
def arraySum {α β : Type*} [AddMonoid β] (value : α → β) (xs : Array α) : β :=
  xs.foldl (fun acc x => acc + value x) 0

theorem arraySum_toList {α β : Type*} [AddMonoid β] (value : α → β)
    (xs : Array α) : arraySum value xs = listSum value xs.toList := by
  unfold arraySum
  rw [← Array.foldl_toList]
  simpa only [zero_add] using listSum_foldl value xs.toList 0

theorem arraySum_append {α β : Type*} [AddMonoid β] (value : α → β)
    (xs ys : Array α) :
    arraySum value (xs ++ ys) = arraySum value xs + arraySum value ys := by
  rw [arraySum_toList, Array.toList_append, listSum_append,
    arraySum_toList, arraySum_toList]

/-- Split an actual Array batch into its two physical extracts. -/
theorem arraySum_split {α β : Type*} [AddMonoid β] (value : α → β)
    (xs : Array α) (n : Nat) (hn : n ≤ xs.size) :
    arraySum value xs = arraySum value (xs.extract 0 n) +
      arraySum value (xs.extract n xs.size) := by
  have he : xs.extract 0 n ++ xs.extract n xs.size = xs := by
    rw [Array.extract_append_extract]
    simp [Nat.max_eq_right hn]
  have h := arraySum_append value (xs.extract 0 n) (xs.extract n xs.size)
  rw [he] at h
  exact h

/-- Any node observable can be aggregated using the checked reader without
evaluating the original finite-state recurrence. Rows need not be distinct. -/
theorem checked_node_listSum_eq {β : Type*} [AddMonoid β]
    (T : CheckedBlockTable) (value : OriginalNode → β) (rows : List Nat) :
    listSum (fun i => value (assembledRead T.blocks i)) rows =
      listSum (fun i => value (originalFinalNodes i)) rows := by
  rw [CheckedBlockTable.read_eq_original T]

theorem checked_node_arraySum_eq {β : Type*} [AddMonoid β]
    (T : CheckedBlockTable) (value : OriginalNode → β) (rows : Array Nat) :
    arraySum (fun i => value (assembledRead T.blocks i)) rows =
      arraySum (fun i => value (originalFinalNodes i)) rows := by
  rw [CheckedBlockTable.read_eq_original T]

def queryLoSum (read : Nat → OriginalNode) (qs : List (Int × Int)) : Int :=
  listSum (fun q => readQueryLo160 read q.1 q.2) qs

def queryHiSum (read : Nat → OriginalNode) (qs : List (Int × Int)) : Int :=
  listSum (fun q => readQueryHi160 read q.1 q.2) qs

/-- Integer batch equality keeps the original rounding on EACH request. -/
theorem checked_query_sums_eq (T : CheckedBlockTable) (qs : List (Int × Int)) :
    queryLoSum (assembledRead T.blocks) qs =
        listSum (fun q => literalQueryLo160 q.1 q.2) qs ∧
      queryHiSum (assembledRead T.blocks) qs =
        listSum (fun q => literalQueryHi160 q.1 q.2) qs := by
  constructor
  · apply listSum_congr
    intro q _
    exact (CheckedBlockTable.query_eq_original T q.1 q.2).1
  · apply listSum_congr
    intro q _
    exact (CheckedBlockTable.query_eq_original T q.1 q.2).2

theorem queryLoSum_append (read : Nat → OriginalNode) (qs rs : List (Int × Int)) :
    queryLoSum read (qs ++ rs) = queryLoSum read qs + queryLoSum read rs := by
  exact listSum_append _ qs rs

theorem queryHiSum_append (read : Nat → OriginalNode) (qs rs : List (Int × Int)) :
    queryHiSum read (qs ++ rs) = queryHiSum read qs + queryHiSum read rs := by
  exact listSum_append _ qs rs

theorem queryLoSum_split (read : Nat → OriginalNode) (qs : List (Int × Int))
    (n : Nat) : queryLoSum read qs =
      queryLoSum read (qs.take n) + queryLoSum read (qs.drop n) := by
  exact listSum_split _ qs n

theorem queryHiSum_split (read : Nat → OriginalNode) (qs : List (Int × Int))
    (n : Nat) : queryHiSum read qs =
      queryHiSum read (qs.take n) + queryHiSum read (qs.drop n) := by
  exact listSum_split _ qs n

/-- Real weights are outside the 160-bit integer query and its rounding. -/
noncomputable def weightedQueryLo (read : Nat → OriginalNode)
    (weight : (Int × Int) → Real) (q : Int × Int) : Real :=
  weight q * ((readQueryLo160 read q.1 q.2 : Real) / 2^160)

noncomputable def weightedQueryHi (read : Nat → OriginalNode)
    (weight : (Int × Int) → Real) (q : Int × Int) : Real :=
  weight q * ((readQueryHi160 read q.1 q.2 : Real) / 2^160)

noncomputable def weightedActualQuery
    (weight : (Int × Int) → Real) (q : Int × Int) : Real :=
  weight q * actualExtendedThirdLowerFactor ((q.1 : Real) / (q.2 : Real))

/-- Batch enclosure is a consequence of the existing individual-query
consumer, with no new analytic or target-enclosure assumption. -/
theorem checked_weighted_query_list_encloses (T : CheckedBlockTable)
    (qs : List (Int × Int)) (weight : (Int × Int) → Real)
    (hweight : ∀ q ∈ qs, 0 ≤ weight q)
    (hvalid : ∀ q ∈ qs, 0 < q.2 ∧ 2*q.2 ≤ q.1 ∧ q.1 ≤ 12*q.2) :
    listSum (weightedQueryLo (assembledRead T.blocks) weight) qs ≤
        listSum (weightedActualQuery weight) qs ∧
      listSum (weightedActualQuery weight) qs ≤
        listSum (weightedQueryHi (assembledRead T.blocks) weight) qs := by
  constructor
  · apply listSum_mono
    intro q hq
    rcases hvalid q hq with ⟨hb, ha2, ha12⟩
    exact mul_le_mul_of_nonneg_left
      (CheckedBlockTable.compact_query_encloses T q.1 q.2 hb ha2 ha12).1
      (hweight q hq)
  · apply listSum_mono
    intro q hq
    rcases hvalid q hq with ⟨hb, ha2, ha12⟩
    exact mul_le_mul_of_nonneg_left
      (CheckedBlockTable.compact_query_encloses T q.1 q.2 hb ha2 ha12).2
      (hweight q hq)

theorem checked_weighted_query_array_encloses (T : CheckedBlockTable)
    (qs : Array (Int × Int)) (weight : (Int × Int) → Real)
    (hweight : ∀ q ∈ qs.toList, 0 ≤ weight q)
    (hvalid : ∀ q ∈ qs.toList, 0 < q.2 ∧ 2*q.2 ≤ q.1 ∧ q.1 ≤ 12*q.2) :
    arraySum (weightedQueryLo (assembledRead T.blocks) weight) qs ≤
        arraySum (weightedActualQuery weight) qs ∧
      arraySum (weightedActualQuery weight) qs ≤
        arraySum (weightedQueryHi (assembledRead T.blocks) weight) qs := by
  simpa only [arraySum_toList] using
    checked_weighted_query_list_encloses T qs.toList weight hweight hvalid

/-- The two accumulated integers, divided once by the unchanged 2^160,
enclose the sum of actual query values. No extra aggregate rounding occurs. -/
theorem checked_query_sum_encloses (T : CheckedBlockTable)
    (qs : List (Int × Int))
    (hvalid : ∀ q ∈ qs, 0 < q.2 ∧ 2*q.2 ≤ q.1 ∧ q.1 ≤ 12*q.2) :
    (queryLoSum (assembledRead T.blocks) qs : Real) / 2^160 ≤
        listSum (fun q => actualExtendedThirdLowerFactor
          ((q.1 : Real) / (q.2 : Real))) qs ∧
      listSum (fun q => actualExtendedThirdLowerFactor
          ((q.1 : Real) / (q.2 : Real))) qs ≤
        (queryHiSum (assembledRead T.blocks) qs : Real) / 2^160 := by
  have h := checked_weighted_query_list_encloses T qs (fun _ => 1)
    (by intro q hq; exact zero_le_one) hvalid
  simpa only [weightedQueryLo, weightedQueryHi, weightedActualQuery, one_mul,
    ← listSum_int_cast_div, queryLoSum, queryHiSum] using h

/-- Concrete y-All40 specialization; the table is consumed unchanged. -/
theorem literal_weighted_query_list_encloses
    (qs : List (Int × Int)) (weight : (Int × Int) → Real)
    (hweight : ∀ q ∈ qs, 0 ≤ weight q)
    (hvalid : ∀ q ∈ qs, 0 < q.2 ∧ 2*q.2 ≤ q.1 ∧ q.1 ≤ 12*q.2) :
    listSum (weightedQueryLo
        (assembledRead ImbalancedChen.OriginalU2All40CheckedTable20261024wSourceOnly.literalBlocks)
        weight) qs ≤ listSum (weightedActualQuery weight) qs ∧
      listSum (weightedActualQuery weight) qs ≤ listSum (weightedQueryHi
        (assembledRead ImbalancedChen.OriginalU2All40CheckedTable20261024wSourceOnly.literalBlocks)
        weight) qs := by
  exact checked_weighted_query_list_encloses
    ImbalancedChen.OriginalU2All40CheckedTable20261024wSourceOnly.literalCheckedBlockTable
    qs weight hweight hvalid

end P0All40ListFold
