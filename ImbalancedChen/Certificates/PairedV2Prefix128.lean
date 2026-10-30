import ImbalancedChen.Certificates.PairedV2Prefix128Data
import ImbalancedChen.Certificates.PairedV2Prefix128Keys000To008
import ImbalancedChen.Certificates.PairedV2Prefix128Keys008To016
import ImbalancedChen.Certificates.PairedV2Prefix128Keys016To024
import ImbalancedChen.Certificates.PairedV2Prefix128Keys024To032
import ImbalancedChen.Certificates.PairedV2Prefix128Keys032To040
import ImbalancedChen.Certificates.PairedV2Prefix128Keys040To048
import ImbalancedChen.Certificates.PairedV2Prefix128Keys048To056
import ImbalancedChen.Certificates.PairedV2Prefix128Keys056To064
import ImbalancedChen.Certificates.PairedV2Prefix128Keys064To072
import ImbalancedChen.Certificates.PairedV2Prefix128Keys072To080
import ImbalancedChen.Certificates.PairedV2Prefix128Keys080To088
import ImbalancedChen.Certificates.PairedV2Prefix128Keys088To096
import ImbalancedChen.Certificates.PairedV2Prefix128Keys096To104
import ImbalancedChen.Certificates.PairedV2Prefix128Keys104To112
import ImbalancedChen.Certificates.PairedV2Prefix128Keys112To120
import ImbalancedChen.Certificates.PairedV2Prefix128Keys120To127
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

set_option maxHeartbeats 4000000 in
/-- Only 127 adjacent checks are needed to certify distinct actual grid pairs. -/
theorem rowKey_adjacent (i : Fin 127) :
    rowKey i.castSucc < rowKey i.succ := by
  fin_cases i
  · exact rowKey_adjacent_000_008 ⟨0, by decide⟩
  · exact rowKey_adjacent_000_008 ⟨1, by decide⟩
  · exact rowKey_adjacent_000_008 ⟨2, by decide⟩
  · exact rowKey_adjacent_000_008 ⟨3, by decide⟩
  · exact rowKey_adjacent_000_008 ⟨4, by decide⟩
  · exact rowKey_adjacent_000_008 ⟨5, by decide⟩
  · exact rowKey_adjacent_000_008 ⟨6, by decide⟩
  · exact rowKey_adjacent_000_008 ⟨7, by decide⟩
  · exact rowKey_adjacent_008_016 ⟨0, by decide⟩
  · exact rowKey_adjacent_008_016 ⟨1, by decide⟩
  · exact rowKey_adjacent_008_016 ⟨2, by decide⟩
  · exact rowKey_adjacent_008_016 ⟨3, by decide⟩
  · exact rowKey_adjacent_008_016 ⟨4, by decide⟩
  · exact rowKey_adjacent_008_016 ⟨5, by decide⟩
  · exact rowKey_adjacent_008_016 ⟨6, by decide⟩
  · exact rowKey_adjacent_008_016 ⟨7, by decide⟩
  · exact rowKey_adjacent_016_024 ⟨0, by decide⟩
  · exact rowKey_adjacent_016_024 ⟨1, by decide⟩
  · exact rowKey_adjacent_016_024 ⟨2, by decide⟩
  · exact rowKey_adjacent_016_024 ⟨3, by decide⟩
  · exact rowKey_adjacent_016_024 ⟨4, by decide⟩
  · exact rowKey_adjacent_016_024 ⟨5, by decide⟩
  · exact rowKey_adjacent_016_024 ⟨6, by decide⟩
  · exact rowKey_adjacent_016_024 ⟨7, by decide⟩
  · exact rowKey_adjacent_024_032 ⟨0, by decide⟩
  · exact rowKey_adjacent_024_032 ⟨1, by decide⟩
  · exact rowKey_adjacent_024_032 ⟨2, by decide⟩
  · exact rowKey_adjacent_024_032 ⟨3, by decide⟩
  · exact rowKey_adjacent_024_032 ⟨4, by decide⟩
  · exact rowKey_adjacent_024_032 ⟨5, by decide⟩
  · exact rowKey_adjacent_024_032 ⟨6, by decide⟩
  · exact rowKey_adjacent_024_032 ⟨7, by decide⟩
  · exact rowKey_adjacent_032_040 ⟨0, by decide⟩
  · exact rowKey_adjacent_032_040 ⟨1, by decide⟩
  · exact rowKey_adjacent_032_040 ⟨2, by decide⟩
  · exact rowKey_adjacent_032_040 ⟨3, by decide⟩
  · exact rowKey_adjacent_032_040 ⟨4, by decide⟩
  · exact rowKey_adjacent_032_040 ⟨5, by decide⟩
  · exact rowKey_adjacent_032_040 ⟨6, by decide⟩
  · exact rowKey_adjacent_032_040 ⟨7, by decide⟩
  · exact rowKey_adjacent_040_048 ⟨0, by decide⟩
  · exact rowKey_adjacent_040_048 ⟨1, by decide⟩
  · exact rowKey_adjacent_040_048 ⟨2, by decide⟩
  · exact rowKey_adjacent_040_048 ⟨3, by decide⟩
  · exact rowKey_adjacent_040_048 ⟨4, by decide⟩
  · exact rowKey_adjacent_040_048 ⟨5, by decide⟩
  · exact rowKey_adjacent_040_048 ⟨6, by decide⟩
  · exact rowKey_adjacent_040_048 ⟨7, by decide⟩
  · exact rowKey_adjacent_048_056 ⟨0, by decide⟩
  · exact rowKey_adjacent_048_056 ⟨1, by decide⟩
  · exact rowKey_adjacent_048_056 ⟨2, by decide⟩
  · exact rowKey_adjacent_048_056 ⟨3, by decide⟩
  · exact rowKey_adjacent_048_056 ⟨4, by decide⟩
  · exact rowKey_adjacent_048_056 ⟨5, by decide⟩
  · exact rowKey_adjacent_048_056 ⟨6, by decide⟩
  · exact rowKey_adjacent_048_056 ⟨7, by decide⟩
  · exact rowKey_adjacent_056_064 ⟨0, by decide⟩
  · exact rowKey_adjacent_056_064 ⟨1, by decide⟩
  · exact rowKey_adjacent_056_064 ⟨2, by decide⟩
  · exact rowKey_adjacent_056_064 ⟨3, by decide⟩
  · exact rowKey_adjacent_056_064 ⟨4, by decide⟩
  · exact rowKey_adjacent_056_064 ⟨5, by decide⟩
  · exact rowKey_adjacent_056_064 ⟨6, by decide⟩
  · exact rowKey_adjacent_056_064 ⟨7, by decide⟩
  · exact rowKey_adjacent_064_072 ⟨0, by decide⟩
  · exact rowKey_adjacent_064_072 ⟨1, by decide⟩
  · exact rowKey_adjacent_064_072 ⟨2, by decide⟩
  · exact rowKey_adjacent_064_072 ⟨3, by decide⟩
  · exact rowKey_adjacent_064_072 ⟨4, by decide⟩
  · exact rowKey_adjacent_064_072 ⟨5, by decide⟩
  · exact rowKey_adjacent_064_072 ⟨6, by decide⟩
  · exact rowKey_adjacent_064_072 ⟨7, by decide⟩
  · exact rowKey_adjacent_072_080 ⟨0, by decide⟩
  · exact rowKey_adjacent_072_080 ⟨1, by decide⟩
  · exact rowKey_adjacent_072_080 ⟨2, by decide⟩
  · exact rowKey_adjacent_072_080 ⟨3, by decide⟩
  · exact rowKey_adjacent_072_080 ⟨4, by decide⟩
  · exact rowKey_adjacent_072_080 ⟨5, by decide⟩
  · exact rowKey_adjacent_072_080 ⟨6, by decide⟩
  · exact rowKey_adjacent_072_080 ⟨7, by decide⟩
  · exact rowKey_adjacent_080_088 ⟨0, by decide⟩
  · exact rowKey_adjacent_080_088 ⟨1, by decide⟩
  · exact rowKey_adjacent_080_088 ⟨2, by decide⟩
  · exact rowKey_adjacent_080_088 ⟨3, by decide⟩
  · exact rowKey_adjacent_080_088 ⟨4, by decide⟩
  · exact rowKey_adjacent_080_088 ⟨5, by decide⟩
  · exact rowKey_adjacent_080_088 ⟨6, by decide⟩
  · exact rowKey_adjacent_080_088 ⟨7, by decide⟩
  · exact rowKey_adjacent_088_096 ⟨0, by decide⟩
  · exact rowKey_adjacent_088_096 ⟨1, by decide⟩
  · exact rowKey_adjacent_088_096 ⟨2, by decide⟩
  · exact rowKey_adjacent_088_096 ⟨3, by decide⟩
  · exact rowKey_adjacent_088_096 ⟨4, by decide⟩
  · exact rowKey_adjacent_088_096 ⟨5, by decide⟩
  · exact rowKey_adjacent_088_096 ⟨6, by decide⟩
  · exact rowKey_adjacent_088_096 ⟨7, by decide⟩
  · exact rowKey_adjacent_096_104 ⟨0, by decide⟩
  · exact rowKey_adjacent_096_104 ⟨1, by decide⟩
  · exact rowKey_adjacent_096_104 ⟨2, by decide⟩
  · exact rowKey_adjacent_096_104 ⟨3, by decide⟩
  · exact rowKey_adjacent_096_104 ⟨4, by decide⟩
  · exact rowKey_adjacent_096_104 ⟨5, by decide⟩
  · exact rowKey_adjacent_096_104 ⟨6, by decide⟩
  · exact rowKey_adjacent_096_104 ⟨7, by decide⟩
  · exact rowKey_adjacent_104_112 ⟨0, by decide⟩
  · exact rowKey_adjacent_104_112 ⟨1, by decide⟩
  · exact rowKey_adjacent_104_112 ⟨2, by decide⟩
  · exact rowKey_adjacent_104_112 ⟨3, by decide⟩
  · exact rowKey_adjacent_104_112 ⟨4, by decide⟩
  · exact rowKey_adjacent_104_112 ⟨5, by decide⟩
  · exact rowKey_adjacent_104_112 ⟨6, by decide⟩
  · exact rowKey_adjacent_104_112 ⟨7, by decide⟩
  · exact rowKey_adjacent_112_120 ⟨0, by decide⟩
  · exact rowKey_adjacent_112_120 ⟨1, by decide⟩
  · exact rowKey_adjacent_112_120 ⟨2, by decide⟩
  · exact rowKey_adjacent_112_120 ⟨3, by decide⟩
  · exact rowKey_adjacent_112_120 ⟨4, by decide⟩
  · exact rowKey_adjacent_112_120 ⟨5, by decide⟩
  · exact rowKey_adjacent_112_120 ⟨6, by decide⟩
  · exact rowKey_adjacent_112_120 ⟨7, by decide⟩
  · exact rowKey_adjacent_120_127 ⟨0, by decide⟩
  · exact rowKey_adjacent_120_127 ⟨1, by decide⟩
  · exact rowKey_adjacent_120_127 ⟨2, by decide⟩
  · exact rowKey_adjacent_120_127 ⟨3, by decide⟩
  · exact rowKey_adjacent_120_127 ⟨4, by decide⟩
  · exact rowKey_adjacent_120_127 ⟨5, by decide⟩
  · exact rowKey_adjacent_120_127 ⟨6, by decide⟩

theorem rowKey_strictMono : StrictMono rowKey :=
  (Fin.strictMono_iff_lt_succ (f := rowKey)).2 rowKey_adjacent

/-- Distinct cumulative ordinals correspond to distinct actual grid cells. -/
theorem rowIndices_injective : Function.Injective rowIndices := by
  intro i j hij
  apply rowKey_strictMono.injective
  unfold rowKey
  rw [hij]

/-- In particular, the new batch contains none of the first four grid cells. -/
theorem prefix_batch_indices_disjoint (i : Fin 64) (j : Fin 64) :
    Prefix64.rowIndices i ≠ Batch64To128.rowIndices j := by
  intro hij
  have hfull : rowIndices (prefixIndex i) = rowIndices (batchIndex j) := by
    simpa only [rowIndices_prefix, rowIndices_batch] using hij
  exact index_ranges_disjoint i j (rowIndices_injective hfull)

/-- Reuse the two established geometry proofs without rechecking old data. -/
theorem geometry_checked (i : Fin 128) :
    E0Geometry (rowIndices i).1 (rowIndices i).2 (rowZ i) := by
  refine Fin.addCases (m := 64) (n := 64) ?_ ?_ i
  · intro j
    simpa only [rowIndices, rowZ, Fin.append_left] using Prefix64.geometry_checked j
  · intro j
    simpa only [rowIndices, rowZ, Fin.append_right] using Batch64To128.geometry_checked j

theorem fibre_argument (i : Fin 128) {t u z w : ℝ}
    (hs : openFibreSupport (rowIndices i).1 (rowIndices i).2 (rowZ i) t u z w) :
    (a : ℝ) < w ∧ w < z ∧ z < u ∧ u < (h : ℝ) ∧
      (h : ℝ) < t ∧ t < (d : ℝ) ∧
      (7 / 3 : ℝ) ≤ (1 - t - u - z - w) / z :=
  (geometry_checked i).fibre_argument hs

theorem fibre_nonempty (i : Fin 128) :
    ∃ t u z w : ℝ,
      openFibreSupport (rowIndices i).1 (rowIndices i).2 (rowZ i) t u z w :=
  (geometry_checked i).fibre_nonempty

/-- The actual integral uses the appended source coordinates directly. -/
noncomputable def rowIntegral (i : Fin 128) : ℝ :=
  pairedLocalIntegral (K : ℝ) a (tLower (rowIndices i).1)
    (tUpper (rowIndices i).1) (uLower (rowIndices i).2)
    (uUpper (rowIndices i).2) (rowZ i)

noncomputable def integral : ℝ := ∑ i : Fin 128, rowIntegral i

@[simp] theorem rowIntegral_prefix (i : Fin 64) :
    rowIntegral (prefixIndex i) = Prefix64.rowIntegral i := by
  simp only [rowIntegral, rowIndices_prefix, rowZ_prefix, Prefix64.rowIntegral]

@[simp] theorem rowIntegral_batch (i : Fin 64) :
    rowIntegral (batchIndex i) = Batch64To128.rowIntegral i := by
  simp only [rowIntegral, rowIndices_batch, rowZ_batch, Batch64To128.rowIntegral]

/-- Exact append relation for the genuine integrals, using the standard
finite-sum partition theorem rather than a geometric union assertion. -/
theorem integral_eq_parts :
    integral = Prefix64.integral + Batch64To128.integral := by
  have hsum := Fin.sum_univ_add (a := 64) (b := 64) rowIntegral
  change integral = (∑ i : Fin 64, rowIntegral (prefixIndex i)) +
    ∑ i : Fin 64, rowIntegral (batchIndex i) at hsum
  simpa only [rowIntegral_prefix, rowIntegral_batch,
    Prefix64.integral, Batch64To128.integral] using hsum

/-- The cumulative sum retains the literal fourfold manuscript kernel. -/
theorem integral_semantics :
    integral = ((K : ℝ) / 80) * ∑ i : Fin 128,
      ∫ t in (tLower (rowIndices i).1 : ℝ)..(tUpper (rowIndices i).1 : ℝ),
      ∫ u in (uLower (rowIndices i).2 : ℝ)..(uUpper (rowIndices i).2 : ℝ),
      ∫ z in (a : ℝ)..(rowZ i : ℝ), ∫ w in (a : ℝ)..z,
        1 / (t * u * z ^ 2 * w) := by
  simp only [integral, rowIntegral, pairedLocalIntegral,
    pairedFibreKernel_eq, Finset.mul_sum]

def lowerBound : ℚ := 406911671777567 / 100000000000000000000

def upperBound : ℚ := 406911907846016 / 100000000000000000000

theorem lowerBound_eq_sum :
    lowerBound = Prefix64.lowerBound + Batch64To128.lowerBound := by
  norm_num [lowerBound, Prefix64.lowerBound, Batch64To128.lowerBound]

theorem upperBound_eq_sum :
    upperBound = Prefix64.upperBound + Batch64To128.upperBound := by
  norm_num [upperBound, Prefix64.upperBound, Batch64To128.upperBound]

/-- Reuse the old four-row bound and append only the new sixty-row bound. -/
theorem integral_bounds :
    (lowerBound : ℝ) ≤ integral ∧ integral ≤ (upperBound : ℝ) := by
  rw [integral_eq_parts]
  constructor
  · simpa only [lowerBound_eq_sum, Rat.cast_add] using
      add_le_add Prefix64.integral_bounds.1 Batch64To128.integral_bounds.1
  · simpa only [upperBound_eq_sum, Rat.cast_add] using
      add_le_add Prefix64.integral_bounds.2 Batch64To128.integral_bounds.2

theorem integral_pos : 0 < integral := by
  exact lt_of_lt_of_le (by norm_num [lowerBound]) integral_bounds.1

end ImbalancedChen.Certificates.PairedV2.Prefix128
