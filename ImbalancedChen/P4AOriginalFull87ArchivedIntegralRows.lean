import ImbalancedChen.P4AOriginalFull87ActualGain
import ImbalancedChen.P4AOriginalFull87CellIndexedArchiveWeight
import ImbalancedChen.P2OriginalSaving16Full87SourceBinding
import ImbalancedChen.P2OriginalSaving16OwnedIntegral
import ImbalancedChen.P2OriginalSaving17DescendingIntegral
import ImbalancedChen.P2OriginalSaving19OwnedIntegral

/-! Original selected numerical entries realized on their own strict cells.
Stages 16 and 17 use individual simplex floors. Stage 19 uses the single
refined lower value on each original simplex, inclusive of its predecessor.
The three finite table-to-witness comparisons are unevaluated. -/
namespace ImbalancedChen.P4AOriginalFull87ArchivedIntegralRows
noncomputable section
open scoped Classical BigOperators
open Set MeasureTheory VariableEnvelope
open P4AOriginalFull87SourceDictionary
open P4AOriginalFull87StrictActionTrim (sourceSet sourceSet_measurable)
open P4AOriginalFull87EighthKernelControl (kernel residual total product kernel_bounds)
open P4AOriginalFull87SourcePrimeTests (cellIntegral)
open P4AOriginalFull87ArchiveSourceIndex (archivedRecordForOriginalCell)

def archived (c : Cell) : ℚ := (archivedRecordForOriginalCell c).2

section Ascending
open P2OriginalSaving16Full87SourceBinding (sourceCell sourceRows_iff_full87_source source_selected_and_cap)
open P2OriginalSaving16OriginalArchive (archive cellFloorNumerator)
open P2OriginalSaving16OwnedIntegral
open P2OriginalSaving16SimplexBinding (rowSupport rowVertices original_row_q96)
open P2OriginalSaving16JensenFloor (q96Floor)
open P2OriginalSaving16OriginalArchive (jensenQ)
open P2OriginalSaving16FourteenPhysicalAtlas (sourceRows cell region sourceDensity_pos_on_region
  integrableOn_sourceDensity_region isOpen_cell)
open P2OriginalAscendingEighthCapDictionary (sourceDensity)

private theorem atlas16 (i : Fin 14) : P2OriginalSaving16OriginalArchive.atlasCell i =
    P2OriginalSaving16Full87SourceBinding.atlasCell i := by fin_cases i <;> decide

private theorem source16 (i : Fin 14) :
    cell (P2OriginalSaving16OriginalArchive.atlasCell i) = sourceSet (sourceCell i) := by
  rw [atlas16]
  ext t
  exact sourceRows_iff_full87_source i t

private theorem density16 {i : Fin 14} {t : Point} (ht : t ∈ sourceSet (sourceCell i)) :
    sourceDensity t = kernel (sourceCell i) t := by
  obtain ⟨_,hM,hR⟩ := source_selected_and_cap i t ((sourceRows_iff_full87_source i t).mpr ht)
  rw [kernel, residual, hR, hM]
  rfl

private def rows16 (i : Fin 14) : Set Point :=
  ⋃ s : Fin (archive i).simplices.size, ownedSupport ⟨i,s⟩

private theorem cell16Floor (i : Fin 14) :
    (cellFloorNumerator i : ℝ)/(2 : ℝ)^96 ≤ cellIntegral (sourceCell i) := by
  have hsum : (cellFloorNumerator i : ℝ)/(2 : ℝ)^96 =
      ∑ s : Fin (archive i).simplices.size, (q96Floor (jensenQ (rowVertices i s)) : ℝ)/(2 : ℝ)^96 := by
    simp [cellFloorNumerator, rowVertices, Finset.sum_div]
  have hU : (∫ t in rows16 i, sourceDensity t) =
      ∑ s : Fin (archive i).simplices.size, ∫ t in rowSupport i s, sourceDensity t := by
    rw [rows16, integral_iUnion_fintype (fun s => ownedSupport_measurable ⟨i,s⟩)
      (fun _ _ h => ownedSupport_same_cell_disjoint i _ _ h) (fun s => ownedSupport_integrable ⟨i,s⟩)]
    exact Finset.sum_congr rfl (fun s _ => ownedSupport_integral ⟨i,s⟩)
  have hsub : rows16 i ⊆ cell (P2OriginalSaving16OriginalArchive.atlasCell i) := by
    intro t ht
    obtain ⟨s,hs⟩ := mem_iUnion.mp ht
    exact ownedSupport_subset_cell ⟨i,s⟩ hs
  have hreg := subset_iUnion cell (P2OriginalSaving16OriginalArchive.atlasCell i)
  have hmono := setIntegral_mono_set (integrableOn_sourceDensity_region.mono_set hreg)
    (show 0 ≤ᵐ[volume.restrict (cell (P2OriginalSaving16OriginalArchive.atlasCell i))] sourceDensity from by
      filter_upwards [ae_restrict_mem (isOpen_cell _).measurableSet] with t ht
      exact (sourceDensity_pos_on_region (hreg ht)).le) (Filter.Eventually.of_forall hsub)
  rw [source16 i] at hmono
  have hd : (∫ t in sourceSet (sourceCell i), sourceDensity t) = cellIntegral (sourceCell i) :=
    setIntegral_congr_fun (sourceSet_measurable _) (fun _ ht => density16 ht)
  rw [hsum, ← hd]
  exact (Finset.sum_le_sum (fun s _ => original_row_q96 i s)).trans (hU.symm.le.trans hmono)

-- The saved integers in the original simplex records avoid recomputing
-- their determinants in this additional, purely archival binding.
private def saved16 (i : Fin 14) : ℤ := ∑ s : Fin (archive i).simplices.size, (archive i).simplices[s].jensenFloor

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem selected16_records :
    ∀ i : Fin 14, archived (sourceCell i) = (saved16 i : ℚ)/(2 : ℚ)^96 := by decide

private theorem saved16_eq (i : Fin 14) : saved16 i = cellFloorNumerator i := by
  apply Finset.sum_congr rfl
  intro s _
  obtain ⟨_,_,_,_,_,_,_,_,_,_,h⟩ := P2OriginalSaving16OriginalArchive.original_simplex_operations i s
  exact h

theorem original16_archived_cell_le_integral (i : Fin 14) :
    (archived (sourceCell i) : ℝ) ≤ cellIntegral (sourceCell i) := by
  rw [selected16_records, saved16_eq]
  exact_mod_cast cell16Floor i
end Ascending

section Descending
open P2OriginalSaving17DescendingArchive (archive cellFloorNumerator)
private def saved17 (i : Fin 15) : ℤ := ∑ s : Fin (archive i).simplices.size, (archive i).simplices[s].jensenFloor

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem selected17_records :
    ∀ i : Fin 15, archived (.descending i) = (saved17 i : ℚ)/(2 : ℚ)^96 := by decide

private theorem saved17_eq (i : Fin 15) : saved17 i = cellFloorNumerator i := by
  apply Finset.sum_congr rfl
  intro s _
  obtain ⟨_,_,_,_,_,_,_,_,_,_,h⟩ := P2OriginalSaving17DescendingArchive.original_simplex_operations i s
  exact h

theorem original17_archived_cell_le_integral (i : Fin 15) :
    (archived (.descending i) : ℝ) ≤ cellIntegral (.descending i) := by
  rw [selected17_records, saved17_eq]
  exact_mod_cast P2OriginalSaving17DescendingIntegral.original_cell_floor_le_full87_source_integral i
end Descending

section AscendingPair
open P2OriginalSaving19OwnedSource (CellRow)
open P2OriginalSaving19Archive (rawMomentRow)
open P2OriginalSaving19OwnedIntegral
open P2OriginalThirdMinorantLogDictionarySourceOnly (conservativeDensity)
open OriginalAscendingThirteenCellOwnership (cell)
open P2OriginalSaving19SourceMeasure (cell_measurable cell_density_integrable cell_density_nonneg)

private def saved19 (i : Fin 13) : ℚ :=
  ∑ s : CellRow i, ((rawMomentRow ⟨i,s⟩).newFloorQ96 : ℚ) / (2 : ℚ)^96

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem selected19_records : ∀ i : Fin 13, archived (.ascendingPair i) = saved19 i := by decide

private theorem source19 (i : Fin 13) : sourceSet (.ascendingPair i) = cell i := by
  ext t
  exact OriginalAscendingThirteenExportOwnershipJoin.strictExportedRows_iff_StrictRows i t

theorem original19_archived_cell_le_integral (i : Fin 13) :
    (archived (.ascendingPair i) : ℝ) ≤ cellIntegral (.ascendingPair i) := by
  let U := ⋃ s : CellRow i, legalOwnedSupport ⟨i,s⟩
  have hU : (∫ t in U, conservativeDensity t) =
      ∑ s : CellRow i, ∫ t in legalOwnedSupport ⟨i,s⟩, conservativeDensity t :=
    integral_iUnion_fintype (fun s => legalOwnedSupport_measurable ⟨i,s⟩)
      (fun _ _ h => legalOwnedSupport_cell_disjoint i _ _ h) (fun s => legalOwnedSupport_integrable ⟨i,s⟩)
  have hsub : U ⊆ cell i := by
    intro t ht
    obtain ⟨s,hs⟩ := mem_iUnion.mp ht
    exact legalOwnedSupport_subset_cell ⟨i,s⟩ hs
  have hm := setIntegral_mono_set (cell_density_integrable i)
    (show 0 ≤ᵐ[volume.restrict (cell i)] conservativeDensity from by
      filter_upwards [ae_restrict_mem (cell_measurable i)] with t ht
      exact cell_density_nonneg ht) (Filter.Eventually.of_forall hsub)
  change (archived (.ascendingPair i) : ℝ) ≤ ∫ t in sourceSet (.ascendingPair i), conservativeDensity t
  rw [source19,selected19_records,saved19,Rat.cast_sum]
  refine (Finset.sum_le_sum (g := fun s : CellRow i => ∫ t in legalOwnedSupport ⟨i,s⟩, conservativeDensity t) ?_).trans (hU.symm.le.trans hm)
  intro s _
  rw [legalOwnedSupport_integral]
  exact P2OriginalSaving19Original28918FloorBinding.saved_row_floor_le_actual_simplex_integral ⟨i,s⟩
end AscendingPair

abbrev Paid := (Fin 14 ⊕ Fin 15) ⊕ Fin 13
def paidCell : Paid → Cell
  | .inl (.inl i) => .remaining (.ascending i)
  | .inl (.inr i) => .descending i
  | .inr i => .ascendingPair i

theorem paidCell_injective : Function.Injective paidCell := by
  rintro ((i|i)|i) ((j|j)|j) h <;> simp_all [paidCell]

theorem paid_cell_le_integral (i : Paid) : (archived (paidCell i) : ℝ) ≤ cellIntegral (paidCell i) := by
  rcases i with (i|i)|i
  · exact original16_archived_cell_le_integral i
  · exact original17_archived_cell_le_integral i
  · exact original19_archived_cell_le_integral i

/-- The exact three cited stage numerators, with stage 19's replacement
used once. The six-stage aggregate additionally has stages 15, 18 and 20. -/
def paidNumerical : ℚ :=
  (1222997719565324892497827 + 467454156274267811817033 + 283388722705335806564439) / 2^96

theorem paid_archive_sum : ∑ i : Paid, archived (paidCell i) = paidNumerical := by decide

theorem paid_numerical_le_full_source : (paidNumerical : ℝ) ≤ ∑ c : Cell, cellIntegral c := by
  classical
  have hmass (c : Cell) : 0 ≤ cellIntegral c := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem (sourceSet_measurable c)] with t ht
    exact (kernel_bounds ht).1
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => paid_cell_le_integral i)
  have heq : (∑ i : Paid, (archived (paidCell i) : ℝ)) = (paidNumerical : ℝ) := by
    exact_mod_cast paid_archive_sum
  rw [heq] at h
  let A : Finset Cell := Finset.univ.image paidCell
  have ha : ∑ c ∈ A, cellIntegral c = ∑ i : Paid, cellIntegral (paidCell i) :=
    Finset.sum_image (fun i _ j _ hij => paidCell_injective hij)
  rw [← ha] at h
  exact h.trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A) (fun c _ _ => hmass c))

/-- Archived lower saving on the actual parent/eighth ordinary difference
of the original schedule. The comparison uses the complete 87-cell policy. -/
theorem exists_original_archived_ordinary_gain (eps : ℝ) (heps : 0 < eps) :
    ∃ r0 : ℕ, ∀ r : ℕ, r0 ≤ r → ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
    ∃ e0 : ℝ, 0 < e0 ∧ ∀ e : ℚ, 0 < e → (e : ℝ) < e0 →
    ∃ q0 : ℕ, 0 < q0 ∧ ∀ q : ℕ, q0 ≤ q → ∀ om : ℝ, om ≤ 1 / 100 →
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
    ∀ (cap : ℕ) (z : ℝ), (N : ℝ)^mu ≤ z → z ≤ cap →
      (paidNumerical : ℝ) - eps < P5OriginalCommonPositivePresieve.normalize N
        (P4AOriginalVariableFifthPhysicalLedger.raw
          (P4AOriginalFull87LicensedSixthPolicy.sixthPolicy n e q om (N : ℝ)) N cap 0 z -
         P4AOriginalVariableFifthPhysicalLedger.raw
          (P4AOriginalFull87LicensedSixthPolicy.policy (P4AOriginalFull87HistoryCore.width r) n e q om
            (N : ℝ)) N cap 0 z) := by
  obtain ⟨r0,hr⟩ := P4AOriginalFull87ActualGain.exists_ordinary_source_gain eps heps
  refine ⟨r0,?_⟩
  intro r hr0
  obtain ⟨n0,hn⟩ := hr r hr0
  refine ⟨n0,?_⟩
  intro n hn0
  obtain ⟨e0,he0,he⟩ := hn n hn0
  refine ⟨e0,he0,?_⟩
  intro e hep hee
  obtain ⟨q0,hq0,hq⟩ := he e hep hee
  refine ⟨q0,hq0,?_⟩
  intro q hqq om hom
  obtain ⟨N0,hN0,hN⟩ := hq q hqq om hom
  refine ⟨N0,hN0,?_⟩
  intro N hNn hEven cap z hz hcap
  exact (sub_le_sub_right paid_numerical_le_full_source eps).trans_lt (hN N hNn hEven cap z hz hcap)

end
end ImbalancedChen.P4AOriginalFull87ArchivedIntegralRows
