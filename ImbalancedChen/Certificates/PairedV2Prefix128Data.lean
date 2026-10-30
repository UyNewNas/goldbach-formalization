import ImbalancedChen.Certificates.PairedV2Prefix64
import ImbalancedChen.Certificates.PairedV2Batch64To128
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Order.Fin.Basic

/-!
# Append adopted rows 64 through 127 to the accepted first four rows

The two inputs retain the exact coordinates from the frozen same-mask-v2
source.  This module uses their existing integral bounds; it does not
repeat the logarithm or integral certificate checks for rows 0 through 3.

Source manuscript: ba6ec11d800eccc54406490631895e174de85766
Source SHA256: f6d31386f93cf77888ea4771ffa549a1cf61dca700bac618ff7646566a02f9b7
Source row ordinals: [0,128), all E0
Prefix row-stream SHA256:
8b2b8ab5ddc4db399044bd8c874eb0b8e4274503366031db6640a4f70dbfa2fa

There are two independent finite checks: the source ordinal ranges form
an exact partition of the first 128 rows, and their actual grid index pairs
are distinct.  The latter follows from 127 adjacent integer inequalities,
not from an assumption that distinct source ordinals imply distinct cells.

The cumulative object is a finite sum of the same genuine fourfold
integrals.  Its decomposition uses `Fin.sum_univ_add`; it does not assert
a geometric union-integral identity, full-mask coverage, or an arithmetic
parent license.  The previous 64 rows are included exactly once.
-/

namespace ImbalancedChen.Certificates.PairedV2.Prefix128

open MeasureTheory Set
open scoped BigOperators Interval

/-- The original first-four ordinal inside the cumulative prefix. -/
def prefixIndex (i : Fin 64) : Fin 128 := Fin.castAdd 64 i

/-- A local new-batch ordinal mapped to original ordinal `64 + i.val`. -/
def batchIndex (i : Fin 64) : Fin 128 := Fin.natAdd 64 i

@[simp] theorem prefixIndex_val (i : Fin 64) :
    (prefixIndex i).val = Prefix64.rowOrdinal i := by
  simp only [prefixIndex, Fin.val_castAdd, Prefix64.rowOrdinal_eq_val]

@[simp] theorem batchIndex_val (i : Fin 64) :
    (batchIndex i).val = Batch64To128.rowOrdinal i := rfl

theorem prefixIndex_range (i : Fin 64) : (prefixIndex i).val < 64 := i.isLt

theorem batchIndex_range (i : Fin 64) :
    64 ≤ (batchIndex i).val ∧ (batchIndex i).val < 128 := by
  have hi := i.isLt
  change 64 ≤ 64 + i.val ∧ 64 + i.val < 128
  omega

/-- The two actual source-ordinal ranges cannot overlap. -/
theorem source_ranges_disjoint (i : Fin 64) (j : Fin 64) :
    Prefix64.rowOrdinal i ≠ Batch64To128.rowOrdinal j := by
  have hi := i.isLt
  simp only [Prefix64.rowOrdinal_eq_val, Batch64To128.rowOrdinal]
  omega

theorem index_ranges_disjoint (i : Fin 64) (j : Fin 64) :
    prefixIndex i ≠ batchIndex j := by
  intro hij
  apply source_ranges_disjoint i j
  simpa only [prefixIndex_val, batchIndex_val] using
    congrArg (fun k : Fin 128 => k.val) hij

/-- Every cumulative row comes from exactly one of the two disjoint ranges. -/
theorem indices_cover (i : Fin 128) :
    (∃ j : Fin 64, i = prefixIndex j) ∨
      (∃ j : Fin 64, i = batchIndex j) := by
  refine Fin.addCases (m := 64) (n := 64) ?_ ?_ i
  · intro j
    exact Or.inl ⟨j, rfl⟩
  · intro j
    exact Or.inr ⟨j, rfl⟩

/-- Exact coverage stated in the original natural-number ordinals. -/
theorem source_ordinal_coverage (n : ℕ) :
    ((∃ i : Fin 64, Prefix64.rowOrdinal i = n) ∨
      (∃ i : Fin 64, Batch64To128.rowOrdinal i = n)) ↔ n < 128 := by
  constructor
  · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
    · have hil := i.isLt
      simp only [Prefix64.rowOrdinal_eq_val] at hi
      omega
    · have hil := i.isLt
      simp only [Batch64To128.rowOrdinal] at hi
      omega
  · intro hn
    by_cases hfirst : n < 64
    · exact Or.inl ⟨⟨n, hfirst⟩, by simp only [Prefix64.rowOrdinal_eq_val]⟩
    · have hlocal : n - 64 < 64 := by omega
      refine Or.inr ⟨⟨n - 64, hlocal⟩, ?_⟩
      change 64 + (n - 64) = n
      omega

def rowIndices : Fin 128 → ℕ × ℕ :=
  Fin.append Prefix64.rowIndices Batch64To128.rowIndices

def rowZ : Fin 128 → ℚ :=
  Fin.append Prefix64.rowZ Batch64To128.rowZ

def rowOrdinal : Fin 128 → ℕ :=
  Fin.append Prefix64.rowOrdinal Batch64To128.rowOrdinal

@[simp] theorem rowIndices_prefix (i : Fin 64) :
    rowIndices (prefixIndex i) = Prefix64.rowIndices i := by
  exact Fin.append_left _ _ i

@[simp] theorem rowIndices_batch (i : Fin 64) :
    rowIndices (batchIndex i) = Batch64To128.rowIndices i := by
  exact Fin.append_right _ _ i

@[simp] theorem rowZ_prefix (i : Fin 64) :
    rowZ (prefixIndex i) = Prefix64.rowZ i := by
  exact Fin.append_left _ _ i

@[simp] theorem rowZ_batch (i : Fin 64) :
    rowZ (batchIndex i) = Batch64To128.rowZ i := by
  exact Fin.append_right _ _ i

/-- The append operation preserves the original row ordinals. -/
theorem rowOrdinal_eq_val (i : Fin 128) : rowOrdinal i = i.val := by
  refine Fin.addCases (m := 64) (n := 64) ?_ ?_ i
  · intro j
    simp only [rowOrdinal, Fin.append_left, Prefix64.rowOrdinal_eq_val, Fin.val_castAdd]
  · intro j
    simp only [rowOrdinal, Fin.append_right, Batch64To128.rowOrdinal, Fin.val_natAdd]

theorem rowOrdinal_injective : Function.Injective rowOrdinal := by
  intro i j hij
  apply Fin.ext
  simpa only [rowOrdinal_eq_val] using hij

/-- An integer key of the actual grid pair, used only for finite ownership. -/
def rowKey (i : Fin 128) : ℕ :=
  512 * (rowIndices i).1 + (rowIndices i).2

end ImbalancedChen.Certificates.PairedV2.Prefix128
