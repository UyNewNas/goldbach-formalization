import ImbalancedChen.P1HistoricalFifthTypedKeyPartition
import ImbalancedChen.P1HistoricalFifthCommonOriginalChargeBinding
import Mathlib

/-!
SOURCE_ONLY / UNCOMPILED_ZERO_CREDIT.
The actual original143 literal blocks, their ordered rows and the original
292633 Fin source positions give the SAME contribution sum. Neither row
values nor masks are deduplicated. The existing F key witness, not a new
decision/replay, supplies original-source uniqueness.
This is a typed-source identity, not an identity with archived NPY bytes.
-/
namespace ImbalancedChen.P1HistoricalFifthOriginalBlockContributions
noncomputable section
open scoped Classical BigOperators
open P1OriginalPrefixRowDecodeSoundness P1HistoricalFifthTypedArchiveShape
open P1HistoricalFifthIndexedOwnerArchive P1HistoricalFifthTypedBaseGeometry
open P1HistoricalFifthTypedKeyPartition

private theorem indexed_list_sum {α : Type*} (xs : List α) (f : α → ℝ) :
    (∑ i : Fin xs.length, f xs[i.val]) = (xs.map f).sum := by
  rw [← List.sum_ofFn]
  have h : List.ofFn (fun i : Fin xs.length => xs[i.val]) = xs := List.ofFn_getElem
  simpa only [List.map_ofFn, Function.comp_def] using
    congrArg (fun ys : List α => (ys.map f).sum) h

private theorem flatMap_block_sum (bs : List (Array FifthWireRow)) (f : FifthWireRow → ℝ) :
    ((bs.flatMap Array.toList).map f).sum =
      (bs.map (fun block => (block.toList.map f).sum)).sum := by
  induction bs with
  | nil => rfl
  | cons block bs ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append,
      List.map_cons, List.sum_cons, ih]

theorem archive_sum_eq_original_row_list (f : FifthWireRow → ℝ) :
    (∑ i : ArchiveIndex, f (archiveRow i)) =
      (Data.P1HistoricalFifthSavedTableData.rows.toList.map f).sum :=
  indexed_list_sum _ f

/-- The RHS is the independently defined ORIGINAL143-block hub itself,
in its original order. It is not a similarly named synthetic family. -/
theorem archive_sum_eq_original_143_blocks (f : FifthWireRow → ℝ) :
    (∑ i : ArchiveIndex, f (archiveRow i)) =
      (Data.P1HistoricalFifthSavedTableData.blocks.toList.map
        (fun block => (block.toList.map f).sum)).sum := by
  rw [archive_sum_eq_original_row_list, rows_toList_order]
  exact flatMap_block_sum _ f

theorem original_block_row_has_unique_source_index
    (block : Array FifthWireRow) (hb : block ∈ Data.P1HistoricalFifthSavedTableData.blocks.toList)
    (raw : FifthWireRow) (hr : raw ∈ block.toList) :
    ∃! i : ArchiveIndex, archiveRow i = raw := by
  have hsource : raw ∈ Data.P1HistoricalFifthSavedTableData.rows.toList := by
    rw [rows_toList_order]
    exact List.mem_flatMap.mpr ⟨block, hb, hr⟩
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hsource
  refine ⟨i, hi, ?_⟩
  intro j hj
  exact archiveRow_injective (hj.trans hi.symm)

theorem original_block_row_baseGeometry
    (block : Array FifthWireRow) (hb : block ∈ Data.P1HistoricalFifthSavedTableData.blocks.toList)
    (raw : FifthWireRow) (hr : raw ∈ block.toList) : baseGeometry raw := by
  obtain ⟨i, hi, _hu⟩ := original_block_row_has_unique_source_index block hb raw hr
  exact hi ▸ archiveRow_baseGeometry i

/-- Extend an arbitrary ORIGINAL-index contribution to a row occurrence.
The finite sum picks its unique original position; it does not silently
convert the original ordered row carrier to a Finset of values. -/
def originalIndexContribution (raw : FifthWireRow) (f : ArchiveIndex → ℝ) : ℝ :=
  ∑ i : ArchiveIndex, if archiveRow i = raw then f i else 0

theorem originalIndexContribution_at_source (i : ArchiveIndex) (f : ArchiveIndex → ℝ) :
    originalIndexContribution (archiveRow i) f = f i := by
  have hsum : (∑ j : ArchiveIndex, if archiveRow j = archiveRow i then f j else 0) =
      (if archiveRow i = archiveRow i then f i else 0) := by
    apply Finset.sum_eq_single i
    · intro j _hj hji
      have hn : archiveRow j ≠ archiveRow i := fun h => hji (archiveRow_injective h)
      exact if_neg hn
    · intro hnot
      exact (hnot (Finset.mem_univ i)).elim
  simpa only [originalIndexContribution, if_pos rfl] using hsum

/-- This form applies to actual source-index gains, strict owner reserves,
and finite Rosser contributions, whose source position must be preserved. -/
theorem indexed_sum_eq_original_143_blocks (f : ArchiveIndex → ℝ) :
    (∑ i : ArchiveIndex, f i) =
      (Data.P1HistoricalFifthSavedTableData.blocks.toList.map (fun block =>
        (block.toList.map (fun raw => originalIndexContribution raw f)).sum)).sum := by
  calc
    _ = ∑ i : ArchiveIndex, originalIndexContribution (archiveRow i) f := by
      exact Finset.sum_congr rfl (fun i _ => (originalIndexContribution_at_source i f).symm)
    _ = _ := archive_sum_eq_original_143_blocks (fun raw => originalIndexContribution raw f)

/-- The original block cut is an exact ordered prefix/suffix identity;
there is no second copy of any tail or gain at the block boundary. -/
theorem original_bank_split_at_block (k : ℕ) (f : FifthWireRow → ℝ) :
    (∑ i : ArchiveIndex, f (archiveRow i)) =
      ((prefixRows k).map f).sum + ((suffixRows k).map f).sum := by
  rw [archive_sum_eq_original_row_list, rows_split_at_block k,
    List.map_append, List.sum_append]

end
end ImbalancedChen.P1HistoricalFifthOriginalBlockContributions
