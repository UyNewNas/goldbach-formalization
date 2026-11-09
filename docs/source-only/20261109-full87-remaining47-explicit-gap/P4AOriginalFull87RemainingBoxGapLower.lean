import ImbalancedChen.P4AOriginalFull87StrictPositiveSourceIntegral
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

New, genuinely numerical LOCAL cap-gap lower bounds on the ORIGINAL
47 remaining-family Source boxes. The 47 cells are 14 ascending, one
seed, 13 nine, two fifty and 17 H5/H7. The previous proof showed that
the original source integrals are strictly positive, but provided no
explicit local integrand margin. Here the pre-existing *original affine
row certificates*, with their correct family indices, are transported
to common Slack row 15, hence to exactly newCap - comparison.

We do not equate the ideal comparison to a physical N-dependent
actualParent, certify the archived selected integrals, or pay an
arithmetic signed reserve. The quantitative integral and all other
40 source-family quantitative endpoint obligations remain open.
-/ 

namespace ImbalancedChen.P4AOriginalFull87RemainingBoxGapLower
noncomputable section

open scoped Classical BigOperators
open VariableEnvelope
open P4AOriginalFull87SourceDictionary
open P4AOriginalFull87EighthKernelControl
open P4AOriginalFull87QuantitativeGapIntegral
open P4AOriginalFull87StrictPositiveSourceIntegral
open P4AOriginalFull87KernelPositiveWitness

private theorem radius_to_large :
    (1 / 100000000 : ℝ) ≤ 1 / 100000 := by norm_num
private theorem radius_to_medium :
    (1 / 100000000 : ℝ) ≤ 1 / 1000000 := by norm_num

/-- The ORIGINAL common source row at position 15 is precisely the
unrounded, original finite-cap gain. No replacement margin is defined. -/
private theorem row15_eq_gap
    (d : P4AOriginalRemainingEighthSources.Cell) (t : Point) :
    P4AOriginalRemainingEighthSources.evalRow
        (P4AOriginalRemainingEighthSources.row d
          (P4AOriginalRemainingEighthSources.commonRow d 15)) t =
      newCap (.remaining d) t - comparison (.remaining d) t := by
  rw [P4AOriginalRemainingEighthSources.source_common_row]
  rfl

/-- Transport each ORIGINAL family-specific row lower bound without
identifying archive order with the source order. The only uniform
weakening is min(1/10000,11/50000,1/20000)=1/20000. -/
theorem original_remaining47_all_rows_lower
    (d : P4AOriginalRemainingEighthSources.Cell) (t : Point)
    (ht : t ∈ sourceInnerBox (.remaining d))
    (k : Fin (P4AOriginalRemainingEighthSources.rowCount d)) :
    (1 / 20000 : ℝ) ≤
      P4AOriginalRemainingEighthSources.evalRow
        (P4AOriginalRemainingEighthSources.row d k) t := by
  cases d with
  | ascending i =>
      have hc : ∀ j : Fin 8,
          |t j - P4AOriginalFull87AscendingAllInteriors.originalAscendingPoint i j| ≤
            (1 / 100000 : ℝ) := by
        intro j
        have hj := (ht j).le
        change |t j - P4AOriginalFull87AscendingAllInteriors.originalAscendingPoint i j| ≤
          (1 / 100000000 : ℝ) at hj
        exact hj.trans radius_to_large
      have h := P4AOriginalFull87AscendingAllInteriors.all14_original_96_rows_box_slack i t hc k
      exact (by norm_num : (1 / 20000 : ℝ) ≤ 1 / 10000).trans
        (by simpa [P4AOriginalRemainingEighthSources.row] using h)
  | seed =>
      have hc : ∀ j : Fin 8,
          |t j - P4AOriginalFull87SeedNineFiftyInteriors.originalPoint 0 j| ≤
            (1 / 100000 : ℝ) := by
        intro j
        have hj := (ht j).le
        change |t j - P4AOriginalFull87SeedNineFiftyInteriors.originalPoint 0 j| ≤
          (1 / 100000000 : ℝ) at hj
        exact hj.trans radius_to_large
      have h := P4AOriginalFull87SeedNineFiftyInteriors.all16_original_rows_box_slack 0 t hc
      exact (by norm_num : (1 / 20000 : ℝ) ≤ 11 / 50000).trans
        (by simpa [P4AOriginalFull87SeedNineFiftyInteriors.originalCell] using h k)
  | nine i =>
      let ix : Fin 16 := ⟨i.val + 1, by omega⟩
      have hc : ∀ j : Fin 8,
          |t j - P4AOriginalFull87SeedNineFiftyInteriors.originalPoint ix j| ≤
            (1 / 100000 : ℝ) := by
        intro j
        have hj := (ht j).le
        change |t j - P4AOriginalFull87SeedNineFiftyInteriors.originalPoint ix j| ≤
          (1 / 100000000 : ℝ) at hj
        exact hj.trans radius_to_large
      have h := P4AOriginalFull87SeedNineFiftyInteriors.all16_original_rows_box_slack ix t hc
      have hlookup :
          P4AOriginalFull87SeedNineFiftyInteriors.originalCell ix = .nine i := by
        fin_cases i <;> decide
      rw [hlookup] at h
      exact (by norm_num : (1 / 20000 : ℝ) ≤ 11 / 50000).trans (h k)
  | fiftyA =>
      have hc : ∀ j : Fin 8,
          |t j - P4AOriginalFull87SeedNineFiftyInteriors.originalPoint 14 j| ≤
            (1 / 100000 : ℝ) := by
        intro j
        have hj := (ht j).le
        change |t j - P4AOriginalFull87SeedNineFiftyInteriors.originalPoint 14 j| ≤
          (1 / 100000000 : ℝ) at hj
        exact hj.trans radius_to_large
      have h := P4AOriginalFull87SeedNineFiftyInteriors.all16_original_rows_box_slack 14 t hc
      exact (by norm_num : (1 / 20000 : ℝ) ≤ 11 / 50000).trans
        (by simpa [P4AOriginalFull87SeedNineFiftyInteriors.originalCell] using h k)
  | fiftyD =>
      have hc : ∀ j : Fin 8,
          |t j - P4AOriginalFull87SeedNineFiftyInteriors.originalPoint 15 j| ≤
            (1 / 100000 : ℝ) := by
        intro j
        have hj := (ht j).le
        change |t j - P4AOriginalFull87SeedNineFiftyInteriors.originalPoint 15 j| ≤
          (1 / 100000000 : ℝ) at hj
        exact hj.trans radius_to_large
      have h := P4AOriginalFull87SeedNineFiftyInteriors.all16_original_rows_box_slack 15 t hc
      exact (by norm_num : (1 / 20000 : ℝ) ≤ 11 / 50000).trans
        (by simpa [P4AOriginalFull87SeedNineFiftyInteriors.originalCell] using h k)
  | h5 i =>
      let ix : Fin 17 := ⟨i.val, by omega⟩
      have hc : ∀ j : Fin 8,
          |t j - P4AOriginalFull87H5H7Interiors.originalPoint ix j| ≤
            (1 / 1000000 : ℝ) := by
        intro j
        have hj := (ht j).le
        change |t j - P4AOriginalFull87H5H7Interiors.originalPoint ix j| ≤
          (1 / 100000000 : ℝ) at hj
        exact hj.trans radius_to_medium
      have h := P4AOriginalFull87H5H7Interiors.all17_original_rows_box_slack ix t hc
      have hlookup : P4AOriginalFull87H5H7Interiors.originalCell ix = .h5 i := by
        fin_cases i <;> decide
      rw [hlookup] at h
      exact h k
  | h7 i =>
      let ix : Fin 17 := ⟨i.val + 7, by omega⟩
      have hc : ∀ j : Fin 8,
          |t j - P4AOriginalFull87H5H7Interiors.originalPoint ix j| ≤
            (1 / 1000000 : ℝ) := by
        intro j
        have hj := (ht j).le
        change |t j - P4AOriginalFull87H5H7Interiors.originalPoint ix j| ≤
          (1 / 100000000 : ℝ) at hj
        exact hj.trans radius_to_medium
      have h := P4AOriginalFull87H5H7Interiors.all17_original_rows_box_slack ix t hc
      have hlookup : P4AOriginalFull87H5H7Interiors.originalCell ix = .h7 i := by
        fin_cases i <;> decide
      rw [hlookup] at h
      exact h k

/-- Explicit strict rational lower bound for the SAME original cap-gap
on the 47 genuine remaining-family inner boxes, not merely a point. -/
theorem original_remaining47_gap_lower
    (d : P4AOriginalRemainingEighthSources.Cell) (t : Point)
    (ht : t ∈ sourceInnerBox (.remaining d)) :
    (1 / 20000 : ℝ) ≤ newCap (.remaining d) t - comparison (.remaining d) t := by
  have h := original_remaining47_all_rows_lower d t ht
    (P4AOriginalRemainingEighthSources.commonRow d 15)
  rwa [row15_eq_gap] at h

/-- Real-valued original EIGHTH kernel, not an N-dependent physical sieve:
on these same 47 boxes the normalized density is bounded explicitly. -/
theorem original_remaining47_kernel_lower
    (d : P4AOriginalRemainingEighthSources.Cell) (t : Point)
    (ht : t ∈ sourceInnerBox (.remaining d)) :
    (4 / (9 * mu ^ 10)) * (1 / 20000 : ℝ) ≤ kernel (.remaining d) t := by
  have hs : Source (.remaining d) t :=
    innerBox_mem_original_source (.remaining d) t ht
  have hmu : 0 < mu := by
    have hlo := source_coordinate_lower hs 0
    exact (cutoff_pos.trans hlo).trans (source_basic hs).1
  have hfactor : 0 ≤ 4 / (9 * mu ^ 10) := by positivity
  have hg := original_remaining47_gap_lower d t ht
  have hscaled :
      (4 / (9 * mu ^ 10)) * (1 / 20000 : ℝ) ≤
        scaledCapGap (.remaining d) t := by
    exact mul_le_mul_of_nonneg_left hg hfactor
  exact hscaled.trans (scaledCapGap_le_kernel hs)

end
end ImbalancedChen.P4AOriginalFull87RemainingBoxGapLower
