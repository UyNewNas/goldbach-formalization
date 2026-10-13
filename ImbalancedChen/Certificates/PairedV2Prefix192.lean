import ImbalancedChen.Certificates.PairedV2Prefix128
import ImbalancedChen.Certificates.PairedV2Batch128To192
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Order.Fin.Basic

/-!
# Append adopted rows 128 through 191 to the accepted first 128 rows

The two inputs retain exact coordinates from the frozen same-mask-v2 source.
This module uses existing integral bounds, and does not recompute the first 128 rows.

Source manuscript: ba6ec11d800eccc54406490631895e174de85766
Source SHA256: f6d31386f93cf77888ea4771ffa549a1cf61dca700bac618ff7646566a02f9b7
Source row ordinals: [0,192), all E0
Prefix row-stream SHA256:
b32c7adb0daff5b9de4da559d4597ff805ed7bd644268b348795fcd52959a8fa

There are two independent finite checks: the source ordinal ranges form
an exact partition of the first 192 rows, and their actual grid index pairs
are distinct.  The latter follows from 191 adjacent integer inequalities,
not from an assumption that distinct source ordinals imply distinct cells.

The cumulative object is a finite sum of the same genuine fourfold
integrals.  Its decomposition uses `Fin.sum_univ_add`; it does not assert
a geometric union-integral identity, full-mask coverage, or an arithmetic
parent license.  The previously certified 128 rows are included exactly once.
-/

namespace ImbalancedChen.Certificates.PairedV2.Prefix192

open MeasureTheory Set
open scoped BigOperators Interval

/-- The original earlier-prefix ordinal inside the cumulative prefix. -/
def prefixIndex (i : Fin 128) : Fin 192 := Fin.castAdd 64 i

/-- A local new-batch ordinal mapped to original ordinal `128 + i.val`. -/
def batchIndex (i : Fin 64) : Fin 192 := Fin.natAdd 128 i

@[simp] theorem prefixIndex_val (i : Fin 128) :
    (prefixIndex i).val = Prefix128.rowOrdinal i := by
  simp only [prefixIndex, Fin.val_castAdd, Prefix128.rowOrdinal_eq_val]

@[simp] theorem batchIndex_val (i : Fin 64) :
    (batchIndex i).val = Batch128To192.rowOrdinal i := rfl

theorem prefixIndex_range (i : Fin 128) : (prefixIndex i).val < 128 := i.isLt

theorem batchIndex_range (i : Fin 64) :
    128 ≤ (batchIndex i).val ∧ (batchIndex i).val < 192 := by
  have hi := i.isLt
  change 128 ≤ 128 + i.val ∧ 128 + i.val < 192
  omega

/-- The two actual source-ordinal ranges cannot overlap. -/
theorem source_ranges_disjoint (i : Fin 128) (j : Fin 64) :
    Prefix128.rowOrdinal i ≠ Batch128To192.rowOrdinal j := by
  have hi := i.isLt
  simp only [Prefix128.rowOrdinal_eq_val, Batch128To192.rowOrdinal]
  omega

theorem index_ranges_disjoint (i : Fin 128) (j : Fin 64) :
    prefixIndex i ≠ batchIndex j := by
  intro hij
  apply source_ranges_disjoint i j
  simpa only [prefixIndex_val, batchIndex_val] using
    congrArg (fun k : Fin 192 => k.val) hij

/-- Every cumulative row comes from exactly one of the two disjoint ranges. -/
theorem indices_cover (i : Fin 192) :
    (∃ j : Fin 128, i = prefixIndex j) ∨
      (∃ j : Fin 64, i = batchIndex j) := by
  refine Fin.addCases (m := 128) (n := 64) ?_ ?_ i
  · intro j
    exact Or.inl ⟨j, rfl⟩
  · intro j
    exact Or.inr ⟨j, rfl⟩

/-- Exact coverage stated in the original natural-number ordinals. -/
theorem source_ordinal_coverage (n : ℕ) :
    ((∃ i : Fin 128, Prefix128.rowOrdinal i = n) ∨
      (∃ i : Fin 64, Batch128To192.rowOrdinal i = n)) ↔ n < 192 := by
  constructor
  · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
    · have hil := i.isLt
      simp only [Prefix128.rowOrdinal_eq_val] at hi
      omega
    · have hil := i.isLt
      simp only [Batch128To192.rowOrdinal] at hi
      omega
  · intro hn
    by_cases hfirst : n < 128
    · exact Or.inl ⟨⟨n, hfirst⟩, by simp only [Prefix128.rowOrdinal_eq_val]⟩
    · have hlocal : n - 128 < 64 := by omega
      refine Or.inr ⟨⟨n - 128, hlocal⟩, ?_⟩
      change 128 + (n - 128) = n
      omega

def rowIndices : Fin 192 → ℕ × ℕ :=
  Fin.append Prefix128.rowIndices Batch128To192.rowIndices

def rowZ : Fin 192 → ℚ :=
  Fin.append Prefix128.rowZ Batch128To192.rowZ

def rowOrdinal : Fin 192 → ℕ :=
  Fin.append Prefix128.rowOrdinal Batch128To192.rowOrdinal

@[simp] theorem rowIndices_prefix (i : Fin 128) :
    rowIndices (prefixIndex i) = Prefix128.rowIndices i := by
  exact Fin.append_left _ _ i

@[simp] theorem rowIndices_batch (i : Fin 64) :
    rowIndices (batchIndex i) = Batch128To192.rowIndices i := by
  exact Fin.append_right _ _ i

@[simp] theorem rowZ_prefix (i : Fin 128) :
    rowZ (prefixIndex i) = Prefix128.rowZ i := by
  exact Fin.append_left _ _ i

@[simp] theorem rowZ_batch (i : Fin 64) :
    rowZ (batchIndex i) = Batch128To192.rowZ i := by
  exact Fin.append_right _ _ i

/-- The append operation preserves the original row ordinals. -/
theorem rowOrdinal_eq_val (i : Fin 192) : rowOrdinal i = i.val := by
  refine Fin.addCases (m := 128) (n := 64) ?_ ?_ i
  · intro j
    simp only [rowOrdinal, Fin.append_left, Prefix128.rowOrdinal_eq_val, Fin.val_castAdd]
  · intro j
    simp only [rowOrdinal, Fin.append_right, Batch128To192.rowOrdinal, Fin.val_natAdd]

theorem rowOrdinal_injective : Function.Injective rowOrdinal := by
  intro i j hij
  apply Fin.ext
  simpa only [rowOrdinal_eq_val] using hij

/-- An integer key of the actual grid pair, used only for finite ownership. -/
def rowKey (i : Fin 192) : ℕ :=
  512 * (rowIndices i).1 + (rowIndices i).2

set_option maxHeartbeats 12000000 in
/-- Only 191 adjacent checks are needed to certify distinct actual grid pairs. -/
theorem rowKey_adjacent (i : Fin 191) :
    rowKey i.castSucc < rowKey i.succ := by
  fin_cases i <;>
    norm_num [rowKey, rowIndices, Fin.append, Fin.addCases,
      Prefix128.rowIndices, Prefix64.rowIndices, Prefix4.rowIndices,
      Batch4To64.rowIndices, Batch64To128.rowIndices, Batch128To192.rowIndices]

theorem rowKey_strictMono : StrictMono rowKey :=
  (Fin.strictMono_iff_lt_succ (f := rowKey)).2 rowKey_adjacent

/-- Distinct cumulative ordinals correspond to distinct actual grid cells. -/
theorem rowIndices_injective : Function.Injective rowIndices := by
  intro i j hij
  apply rowKey_strictMono.injective
  unfold rowKey
  rw [hij]

/-- In particular, the new batch contains none of the preceding 128 grid cells. -/
theorem prefix_batch_indices_disjoint (i : Fin 128) (j : Fin 64) :
    Prefix128.rowIndices i ≠ Batch128To192.rowIndices j := by
  intro hij
  have hfull : rowIndices (prefixIndex i) = rowIndices (batchIndex j) := by
    simpa only [rowIndices_prefix, rowIndices_batch] using hij
  exact index_ranges_disjoint i j (rowIndices_injective hfull)

/-- Reuse the two established geometry proofs without rechecking old data. -/
theorem geometry_checked (i : Fin 192) :
    E0Geometry (rowIndices i).1 (rowIndices i).2 (rowZ i) := by
  refine Fin.addCases (m := 128) (n := 64) ?_ ?_ i
  · intro j
    simpa only [rowIndices, rowZ, Fin.append_left] using Prefix128.geometry_checked j
  · intro j
    simpa only [rowIndices, rowZ, Fin.append_right] using Batch128To192.geometry_checked j

theorem fibre_argument (i : Fin 192) {t u z w : ℝ}
    (hs : openFibreSupport (rowIndices i).1 (rowIndices i).2 (rowZ i) t u z w) :
    (a : ℝ) < w ∧ w < z ∧ z < u ∧ u < (h : ℝ) ∧
      (h : ℝ) < t ∧ t < (d : ℝ) ∧
      (7 / 3 : ℝ) ≤ (1 - t - u - z - w) / z :=
  (geometry_checked i).fibre_argument hs

theorem fibre_nonempty (i : Fin 192) :
    ∃ t u z w : ℝ,
      openFibreSupport (rowIndices i).1 (rowIndices i).2 (rowZ i) t u z w :=
  (geometry_checked i).fibre_nonempty

/-- The actual integral uses the appended source coordinates directly. -/
noncomputable def rowIntegral (i : Fin 192) : ℝ :=
  pairedLocalIntegral (K : ℝ) a (tLower (rowIndices i).1)
    (tUpper (rowIndices i).1) (uLower (rowIndices i).2)
    (uUpper (rowIndices i).2) (rowZ i)

noncomputable def integral : ℝ := ∑ i : Fin 192, rowIntegral i

@[simp] theorem rowIntegral_prefix (i : Fin 128) :
    rowIntegral (prefixIndex i) = Prefix128.rowIntegral i := by
  simp only [rowIntegral, rowIndices_prefix, rowZ_prefix, Prefix128.rowIntegral]

@[simp] theorem rowIntegral_batch (i : Fin 64) :
    rowIntegral (batchIndex i) = Batch128To192.rowIntegral i := by
  simp only [rowIntegral, rowIndices_batch, rowZ_batch, Batch128To192.rowIntegral]

/-- Exact append relation for the genuine integrals, using the standard
finite-sum partition theorem rather than a geometric union assertion. -/
theorem integral_eq_parts :
    integral = Prefix128.integral + Batch128To192.integral := by
  have hsum := Fin.sum_univ_add (a := 128) (b := 64) rowIntegral
  change integral = (∑ i : Fin 128, rowIntegral (prefixIndex i)) +
    ∑ i : Fin 64, rowIntegral (batchIndex i) at hsum
  simpa only [rowIntegral_prefix, rowIntegral_batch,
    Prefix128.integral, Batch128To192.integral] using hsum

/-- The cumulative sum retains the literal fourfold manuscript kernel. -/
theorem integral_semantics :
    integral = ((K : ℝ) / 80) * ∑ i : Fin 192,
      ∫ t in (tLower (rowIndices i).1 : ℝ)..(tUpper (rowIndices i).1 : ℝ),
      ∫ u in (uLower (rowIndices i).2 : ℝ)..(uUpper (rowIndices i).2 : ℝ),
      ∫ z in (a : ℝ)..(rowZ i : ℝ), ∫ w in (a : ℝ)..z,
        1 / (t * u * z ^ 2 * w) := by
  simp only [integral, rowIntegral, pairedLocalIntegral,
    pairedFibreKernel_eq, Finset.mul_sum]

def lowerBound : ℚ := 610834375909440 / 100000000000000000000

def upperBound : ℚ := 610834730821178 / 100000000000000000000

theorem lowerBound_eq_sum :
    lowerBound = Prefix128.lowerBound + Batch128To192.lowerBound := by
  norm_num [lowerBound, Prefix128.lowerBound, Batch128To192.lowerBound]

theorem upperBound_eq_sum :
    upperBound = Prefix128.upperBound + Batch128To192.upperBound := by
  norm_num [upperBound, Prefix128.upperBound, Batch128To192.upperBound]

/-- Reuse the old four-row bound and append only the new sixty-row bound. -/
theorem integral_bounds :
    (lowerBound : ℝ) ≤ integral ∧ integral ≤ (upperBound : ℝ) := by
  rw [integral_eq_parts]
  constructor
  · simpa only [lowerBound_eq_sum, Rat.cast_add] using
      add_le_add Prefix128.integral_bounds.1 Batch128To192.integral_bounds.1
  · simpa only [upperBound_eq_sum, Rat.cast_add] using
      add_le_add Prefix128.integral_bounds.2 Batch128To192.integral_bounds.2

theorem integral_pos : 0 < integral := by
  exact lt_of_lt_of_le (by norm_num [lowerBound]) integral_bounds.1

end ImbalancedChen.Certificates.PairedV2.Prefix192
