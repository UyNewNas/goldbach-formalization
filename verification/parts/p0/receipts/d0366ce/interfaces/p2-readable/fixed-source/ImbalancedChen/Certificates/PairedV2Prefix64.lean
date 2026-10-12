import ImbalancedChen.Certificates.PairedV2Prefix4
import ImbalancedChen.Certificates.PairedV2Batch4To64
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Order.Fin.Basic

/-!
# Append adopted rows 4 through 63 to the accepted first four rows

The two inputs retain the exact coordinates from the frozen same-mask-v2
source.  This module uses their existing integral bounds; it does not
repeat the logarithm or integral certificate checks for rows 0 through 3.

Source manuscript: ba6ec11d800eccc54406490631895e174de85766
Source SHA256: f6d31386f93cf77888ea4771ffa549a1cf61dca700bac618ff7646566a02f9b7
Source row ordinals: [0,64), all E0
Prefix row-stream SHA256:
f89caa496a9672c1dc9285a22f1e010008a0d6ea6e9ff850fb09747586afaaf9

There are two independent finite checks: the source ordinal ranges form
an exact partition of the first 64 rows, and their actual grid index pairs
are distinct.  The latter follows from 63 adjacent integer inequalities,
not from an assumption that distinct source ordinals imply distinct cells.

The cumulative object is a finite sum of the same genuine fourfold
integrals.  Its decomposition uses `Fin.sum_univ_add`; it does not assert
a geometric union-integral identity, full-mask coverage, or an arithmetic
parent license.  The first four rows are included exactly once.
-/

namespace ImbalancedChen.Certificates.PairedV2.Prefix64

open MeasureTheory Set
open scoped BigOperators Interval

/-- The original first-four ordinal inside the cumulative prefix. -/
def prefixIndex (i : Fin 4) : Fin 64 := Fin.castAdd 60 i

/-- A local new-batch ordinal mapped to original ordinal `4 + i.val`. -/
def batchIndex (i : Fin 60) : Fin 64 := Fin.natAdd 4 i

@[simp] theorem prefixIndex_val (i : Fin 4) :
    (prefixIndex i).val = Prefix4.rowOrdinal i := rfl

@[simp] theorem batchIndex_val (i : Fin 60) :
    (batchIndex i).val = Batch4To64.rowOrdinal i := rfl

theorem prefixIndex_range (i : Fin 4) : (prefixIndex i).val < 4 := i.isLt

theorem batchIndex_range (i : Fin 60) :
    4 ≤ (batchIndex i).val ∧ (batchIndex i).val < 64 := by
  have hi := i.isLt
  change 4 ≤ 4 + i.val ∧ 4 + i.val < 64
  omega

/-- The two actual source-ordinal ranges cannot overlap. -/
theorem source_ranges_disjoint (i : Fin 4) (j : Fin 60) :
    Prefix4.rowOrdinal i ≠ Batch4To64.rowOrdinal j := by
  have hi := i.isLt
  simp only [Prefix4.rowOrdinal, Batch4To64.rowOrdinal]
  omega

theorem index_ranges_disjoint (i : Fin 4) (j : Fin 60) :
    prefixIndex i ≠ batchIndex j := by
  intro hij
  apply source_ranges_disjoint i j
  simpa only [prefixIndex_val, batchIndex_val] using
    congrArg (fun k : Fin 64 => k.val) hij

/-- Every cumulative row comes from exactly one of the two disjoint ranges. -/
theorem indices_cover (i : Fin 64) :
    (∃ j : Fin 4, i = prefixIndex j) ∨
      (∃ j : Fin 60, i = batchIndex j) := by
  refine Fin.addCases (m := 4) (n := 60) ?_ ?_ i
  · intro j
    exact Or.inl ⟨j, rfl⟩
  · intro j
    exact Or.inr ⟨j, rfl⟩

/-- Exact coverage stated in the original natural-number ordinals. -/
theorem source_ordinal_coverage (n : ℕ) :
    ((∃ i : Fin 4, Prefix4.rowOrdinal i = n) ∨
      (∃ i : Fin 60, Batch4To64.rowOrdinal i = n)) ↔ n < 64 := by
  constructor
  · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
    · have hil := i.isLt
      simp only [Prefix4.rowOrdinal] at hi
      omega
    · have hil := i.isLt
      simp only [Batch4To64.rowOrdinal] at hi
      omega
  · intro hn
    by_cases hfirst : n < 4
    · exact Or.inl ⟨⟨n, hfirst⟩, rfl⟩
    · have hlocal : n - 4 < 60 := by omega
      refine Or.inr ⟨⟨n - 4, hlocal⟩, ?_⟩
      change 4 + (n - 4) = n
      omega

def rowIndices : Fin 64 → ℕ × ℕ :=
  Fin.append Prefix4.rowIndices Batch4To64.rowIndices

def rowZ : Fin 64 → ℚ :=
  Fin.append Prefix4.rowZ Batch4To64.rowZ

def rowOrdinal : Fin 64 → ℕ :=
  Fin.append Prefix4.rowOrdinal Batch4To64.rowOrdinal

@[simp] theorem rowIndices_prefix (i : Fin 4) :
    rowIndices (prefixIndex i) = Prefix4.rowIndices i := by
  exact Fin.append_left _ _ i

@[simp] theorem rowIndices_batch (i : Fin 60) :
    rowIndices (batchIndex i) = Batch4To64.rowIndices i := by
  exact Fin.append_right _ _ i

@[simp] theorem rowZ_prefix (i : Fin 4) :
    rowZ (prefixIndex i) = Prefix4.rowZ i := by
  exact Fin.append_left _ _ i

@[simp] theorem rowZ_batch (i : Fin 60) :
    rowZ (batchIndex i) = Batch4To64.rowZ i := by
  exact Fin.append_right _ _ i

/-- The append operation preserves the original row ordinals. -/
theorem rowOrdinal_eq_val (i : Fin 64) : rowOrdinal i = i.val := by
  refine Fin.addCases (m := 4) (n := 60) ?_ ?_ i
  · intro j
    simp only [rowOrdinal, Fin.append_left, Prefix4.rowOrdinal, Fin.val_castAdd]
  · intro j
    simp only [rowOrdinal, Fin.append_right, Batch4To64.rowOrdinal, Fin.val_natAdd]

theorem rowOrdinal_injective : Function.Injective rowOrdinal := by
  intro i j hij
  apply Fin.ext
  simpa only [rowOrdinal_eq_val] using hij

/-- An integer key of the actual grid pair, used only for finite ownership. -/
def rowKey (i : Fin 64) : ℕ :=
  512 * (rowIndices i).1 + (rowIndices i).2

set_option maxHeartbeats 1000000 in
/-- Only 63 adjacent checks are needed to certify distinct actual grid pairs. -/
theorem rowKey_adjacent (i : Fin 63) :
    rowKey i.castSucc < rowKey i.succ := by
  fin_cases i <;>
    norm_num [rowKey, rowIndices, Fin.append, Fin.addCases,
      Prefix4.rowIndices, Batch4To64.rowIndices]

theorem rowKey_strictMono : StrictMono rowKey :=
  (Fin.strictMono_iff_lt_succ (f := rowKey)).2 rowKey_adjacent

/-- Distinct cumulative ordinals correspond to distinct actual grid cells. -/
theorem rowIndices_injective : Function.Injective rowIndices := by
  intro i j hij
  apply rowKey_strictMono.injective
  unfold rowKey
  rw [hij]

/-- In particular, the new batch contains none of the first four grid cells. -/
theorem prefix_batch_indices_disjoint (i : Fin 4) (j : Fin 60) :
    Prefix4.rowIndices i ≠ Batch4To64.rowIndices j := by
  intro hij
  have hfull : rowIndices (prefixIndex i) = rowIndices (batchIndex j) := by
    simpa only [rowIndices_prefix, rowIndices_batch] using hij
  exact index_ranges_disjoint i j (rowIndices_injective hfull)

/-- Reuse the two established geometry proofs without rechecking old data. -/
theorem geometry_checked (i : Fin 64) :
    E0Geometry (rowIndices i).1 (rowIndices i).2 (rowZ i) := by
  refine Fin.addCases (m := 4) (n := 60) ?_ ?_ i
  · intro j
    simpa only [rowIndices, rowZ, Fin.append_left] using Prefix4.geometry_checked j
  · intro j
    simpa only [rowIndices, rowZ, Fin.append_right] using Batch4To64.geometry_checked j

theorem fibre_argument (i : Fin 64) {t u z w : ℝ}
    (hs : openFibreSupport (rowIndices i).1 (rowIndices i).2 (rowZ i) t u z w) :
    (a : ℝ) < w ∧ w < z ∧ z < u ∧ u < (h : ℝ) ∧
      (h : ℝ) < t ∧ t < (d : ℝ) ∧
      (7 / 3 : ℝ) ≤ (1 - t - u - z - w) / z :=
  (geometry_checked i).fibre_argument hs

theorem fibre_nonempty (i : Fin 64) :
    ∃ t u z w : ℝ,
      openFibreSupport (rowIndices i).1 (rowIndices i).2 (rowZ i) t u z w :=
  (geometry_checked i).fibre_nonempty

/-- The actual integral uses the appended source coordinates directly. -/
noncomputable def rowIntegral (i : Fin 64) : ℝ :=
  pairedLocalIntegral (K : ℝ) a (tLower (rowIndices i).1)
    (tUpper (rowIndices i).1) (uLower (rowIndices i).2)
    (uUpper (rowIndices i).2) (rowZ i)

noncomputable def integral : ℝ := ∑ i : Fin 64, rowIntegral i

@[simp] theorem rowIntegral_prefix (i : Fin 4) :
    rowIntegral (prefixIndex i) = Prefix4.rowIntegral i := by
  simp only [rowIntegral, rowIndices_prefix, rowZ_prefix, Prefix4.rowIntegral]

@[simp] theorem rowIntegral_batch (i : Fin 60) :
    rowIntegral (batchIndex i) = Batch4To64.rowIntegral i := by
  simp only [rowIntegral, rowIndices_batch, rowZ_batch, Batch4To64.rowIntegral]

/-- Exact append relation for the genuine integrals, using the standard
finite-sum partition theorem rather than a geometric union assertion. -/
theorem integral_eq_parts :
    integral = Prefix4.integral + Batch4To64.integral := by
  have hsum := Fin.sum_univ_add (a := 4) (b := 60) rowIntegral
  change integral = (∑ i : Fin 4, rowIntegral (prefixIndex i)) +
    ∑ i : Fin 60, rowIntegral (batchIndex i) at hsum
  simpa only [rowIntegral_prefix, rowIntegral_batch,
    Prefix4.integral, Batch4To64.integral] using hsum

/-- The cumulative sum retains the literal fourfold manuscript kernel. -/
theorem integral_semantics :
    integral = ((K : ℝ) / 80) * ∑ i : Fin 64,
      ∫ t in (tLower (rowIndices i).1 : ℝ)..(tUpper (rowIndices i).1 : ℝ),
      ∫ u in (uLower (rowIndices i).2 : ℝ)..(uUpper (rowIndices i).2 : ℝ),
      ∫ z in (a : ℝ)..(rowZ i : ℝ), ∫ w in (a : ℝ)..z,
        1 / (t * u * z ^ 2 * w) := by
  simp only [integral, rowIntegral, pairedLocalIntegral,
    pairedFibreKernel_eq, Finset.mul_sum]

def lowerBound : ℚ := 203256527543633 / 100000000000000000000

def upperBound : ℚ := 50814161308597 / 25000000000000000000

theorem lowerBound_eq_sum :
    lowerBound = Prefix4.lowerBound + Batch4To64.lowerBound := by
  norm_num [lowerBound, Prefix4.lowerBound, Batch4To64.lowerBound]

theorem upperBound_eq_sum :
    upperBound = Prefix4.upperBound + Batch4To64.upperBound := by
  norm_num [upperBound, Prefix4.upperBound, Batch4To64.upperBound]

/-- Reuse the old four-row bound and append only the new sixty-row bound. -/
theorem integral_bounds :
    (lowerBound : ℝ) ≤ integral ∧ integral ≤ (upperBound : ℝ) := by
  rw [integral_eq_parts]
  constructor
  · simpa only [lowerBound_eq_sum, Rat.cast_add] using
      add_le_add Prefix4.integral_bounds.1 Batch4To64.integral_bounds.1
  · simpa only [upperBound_eq_sum, Rat.cast_add] using
      add_le_add Prefix4.integral_bounds.2 Batch4To64.integral_bounds.2

theorem integral_pos : 0 < integral := by
  exact lt_of_lt_of_le (by norm_num [lowerBound]) integral_bounds.1

end ImbalancedChen.Certificates.PairedV2.Prefix64
