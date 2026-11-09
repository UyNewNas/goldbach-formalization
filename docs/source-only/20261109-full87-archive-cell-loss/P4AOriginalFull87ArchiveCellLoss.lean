import ImbalancedChen.P4AOriginalFull87CellIndexedArchiveWeight
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
An exact per-Cell stability invoice for the ORIGINAL 87 frozen numerical
archive, indexed by the ORIGINAL Cell and its globalIndex bijection.

This is an archive-only claim. It does not identify a saved rational number
with a physical N-dependent signed gain, nor pay a compiler or density reserve.
No external distribution assertion is used.
-/

namespace ImbalancedChen.P4AOriginalFull87ArchiveCellLoss

noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87SourceDictionary
open P4AOriginalFull87ArchiveSourceIndex
open P4AOriginalFull87CellIndexedArchiveWeight

/-- Original per-Cell frozen selected rational, not a physical occurrence. -/
private def gain (c : Cell) : ℚ :=
  (archivedRecordForOriginalCell c).2

/-- The smallest of the 87 archived rational selected values. -/
def archiveFloor : ℚ :=
  (111654814435 : ℚ) / 79228162514264337593543950336

/-- Finite proof obligation on the actual frozen 87-row table, not a
caller-provided positivity premise. This computes all 87 literal rows. -/
theorem archive_all_indices_above_floor :
    ∀ i : Fin 87, archiveFloor ≤ (sourceIndexRecord i).2 := by
  decide

/-- The minimum occurs in the original H5 first-failure Cell 0, whose
global index is 70. No synthetic 88th Cell is introduced. -/
theorem archive_floor_is_attained :
    gain (.remaining (.h5 (0 : Fin 7))) = archiveFloor := by
  decide

/-- The archived value for EACH original Cell is positive, including
the tiny H5-00 record. This is NOT a statement about actual signed gains. -/
theorem archive_cell_positive (c : Cell) : 0 < gain c := by
  have h := archive_all_indices_above_floor (globalIndex c)
  have hfloor : 0 < archiveFloor := by
    norm_num [archiveFloor]
  exact lt_of_lt_of_le hfloor h

/-- A cell-specific loss invoice for the actual frozen 87-row numerical
table. Each archive record is charged once at its ORIGINAL Cell index.
Different cells may have different relative perturbation bounds.
This does not establish such a bound for an N-dependent physical producer. -/
theorem archive_cellwise_weight_loss
    (w allowance : Cell → ℚ)
    (hallow : ∀ c : Cell, |w c - 1| ≤ allowance c) :
    |(∑ c : Cell, w c * gain c) -
      ((3111307568597708509491143 : ℚ) /
        79228162514264337593543950336)| ≤
      ∑ c : Cell, allowance c * gain c := by
  have htotal :
      (∑ c : Cell, gain c) =
        ((3111307568597708509491143 : ℚ) /
          79228162514264337593543950336) := by
    exact original_cell_archive_selected_sum_exact
  have hdifference :
      (∑ c : Cell, w c * gain c) - (∑ c : Cell, gain c) =
        ∑ c : Cell, (w c - 1) * gain c := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro c _
    ring
  calc
    |(∑ c : Cell, w c * gain c) -
        ((3111307568597708509491143 : ℚ) /
          79228162514264337593543950336)| =
        |∑ c : Cell, (w c - 1) * gain c| := by
          rw [← htotal, hdifference]
    _ ≤ ∑ c : Cell, |(w c - 1) * gain c| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ c : Cell, |w c - 1| * gain c := by
      apply Finset.sum_congr rfl
      intro c _
      rw [abs_mul, abs_of_pos (archive_cell_positive c)]
    _ ≤ ∑ c : Cell, allowance c * gain c := by
      apply Finset.sum_le_sum
      intro c _
      exact mul_le_mul_of_nonneg_right (hallow c)
        (le_of_lt (archive_cell_positive c))

/-- Uniform relative-weight error gives an exact total-archive invoice.
It is an algebraic sensitivity statement and is NOT an already-paid
estimate for the actual prime receiver or signed sieve. -/
theorem archive_uniform_weight_loss (w : Cell → ℚ) (eps : ℚ)
    (hweight : ∀ c : Cell, |w c - 1| ≤ eps) :
    |(∑ c : Cell, w c * gain c) -
      ((3111307568597708509491143 : ℚ) /
        79228162514264337593543950336)| ≤
      eps * ((3111307568597708509491143 : ℚ) /
        79228162514264337593543950336) := by
  calc
    _ ≤ ∑ c : Cell, eps * gain c :=
      archive_cellwise_weight_loss w (fun _ => eps) hweight
    _ = eps * (∑ c : Cell, gain c) := by
      rw [Finset.mul_sum]
    _ = _ := by
      rw [original_cell_archive_selected_sum_exact]

end
end ImbalancedChen.P4AOriginalFull87ArchiveCellLoss
