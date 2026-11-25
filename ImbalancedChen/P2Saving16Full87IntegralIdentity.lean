import ImbalancedChen.P2OriginalSaving16CellOwnership
import ImbalancedChen.P2OriginalSaving16Full87SourceBinding
import ImbalancedChen.P4AOriginalFull87IntegralDefinitions

/-!
The original saving16 integral is exactly the sum of its fourteen entries
in the original full87 source dictionary. The source cells are strictly
pairwise disjoint by the existing literal-pattern ownership theorem. The
full87 kernel agrees with the saving16 density on each of these sources.

The final identity partitions the existing full87 sum into these fourteen
entries and its other seventy-three entries. It adds no second saving and
introduces no policy, asymptotic, numerical-floor or compiler premise.
This source has not been elaborated or kernel-checked in this session.
-/

namespace ImbalancedChen.P2Saving16Full87IntegralIdentity

noncomputable section
open scoped Classical BigOperators
open Set MeasureTheory
open P2OriginalAscendingEighthCapDictionary (sourceDensity)
open P2OriginalSaving16FourteenPhysicalAtlas (cell region isOpen_cell)
open P2OriginalSaving16Full87SourceBinding
  (AtlasCell FullCell atlasCell atlasCell_bijective sourceCell
    sourceRows_iff_full87_source source_selected_and_cap)
open P4AOriginalFull87StrictActionTrim (sourceSet)
open P4AOriginalFull87EighthKernelControl (kernel residual)
open P4AOriginalFull87SourcePrimeTests (cellIntegral)

/-- The fourteen entries use distinct constructors of the original type. -/
theorem sourceCell_injective : Function.Injective sourceCell := by
  intro i j h
  simpa only [sourceCell, P4AOriginalFull87SourceDictionary.Cell.remaining.injEq,
    P4AOriginalRemainingEighthSources.Cell.ascending.injEq] using h

/-- Every original strict affine row is retained in this set identity. -/
theorem atlasCell_eq_sourceSet (i : Fin 14) :
    cell (atlasCell i) = sourceSet (sourceCell i) := by
  ext t
  exact sourceRows_iff_full87_source i t

/-- The original comparison R and buffered cap M give the same factor-four
kernel with both residual denominators and all eight coordinate factors. -/
theorem sourceDensity_eq_kernel (i : Fin 14) (t : Fin 8 → ℝ)
    (ht : t ∈ sourceSet (sourceCell i)) :
    sourceDensity t = kernel (sourceCell i) t := by
  obtain ⟨_, hM, hR⟩ := source_selected_and_cap i t
    ((sourceRows_iff_full87_source i t).mpr ht)
  rw [kernel, residual, hR, hM]
  rfl

/-- No new trim or cutoff enters the integral on the full87 side. -/
theorem atlasCell_integral_eq (i : Fin 14) :
    (∫ t in cell (atlasCell i), sourceDensity t) = cellIntegral (sourceCell i) := by
  rw [atlasCell_eq_sourceSet]
  change (∫ t in sourceSet (sourceCell i), sourceDensity t) =
    ∫ t in sourceSet (sourceCell i), kernel (sourceCell i) t
  apply setIntegral_congr_fun
  · rw [← atlasCell_eq_sourceSet i]
    exact (isOpen_cell (atlasCell i)).measurableSet
  · intro t ht
    exact sourceDensity_eq_kernel i t ht

/-- The already proved strict-cell ownership and a bijective reindexing
identify the whole original fourteen-cell integral with its full87 entries. -/
theorem region_integral_eq_sum_full87_cells :
    (∫ t in region, sourceDensity t) =
      ∑ i : Fin 14, cellIntegral (sourceCell i) := by
  calc
    _ = ∑ c : AtlasCell, ∫ t in cell c, sourceDensity t :=
      P2OriginalSaving16CellOwnership.region_integral_eq_sum_cells
    _ = ∑ i : Fin 14, ∫ t in cell (atlasCell i), sourceDensity t :=
      (Equiv.sum_comp (Equiv.ofBijective atlasCell atlasCell_bijective)
        (fun c : AtlasCell => ∫ t in cell c, sourceDensity t)).symm
    _ = ∑ i : Fin 14, cellIntegral (sourceCell i) :=
      Finset.sum_congr rfl (fun i _ => atlasCell_integral_eq i)

/-- Precisely the original fourteen ascending entries; seed7 is excluded. -/
def sourceCells : Finset FullCell := Finset.univ.image sourceCell

/-- The remaining original entries are kept with their complete integrals. -/
def otherCells : Finset FullCell := Finset.univ \ sourceCells

theorem sourceCells_card : sourceCells.card = 14 := by
  rw [sourceCells, Finset.card_image_of_injective _ sourceCell_injective]
  simp

theorem otherCells_card : otherCells.card = 73 := by
  rw [otherCells, Finset.card_sdiff_of_subset (Finset.subset_univ sourceCells),
    Finset.card_univ, P4AOriginalFull87SourceDictionary.source_cell_count, sourceCells_card]

theorem sourceCells_integral_sum :
    (∑ c ∈ sourceCells, cellIntegral c) =
      ∑ i : Fin 14, cellIntegral (sourceCell i) := by
  exact Finset.sum_image (fun i _ j _ h => sourceCell_injective h)

/-- Exact bookkeeping in the original full87 sum. The fourteen-cell
integral occurs once, together with all seventy-three other source integrals. -/
theorem full87_integral_eq_fourteen_add_complement :
    (∑ c : FullCell, cellIntegral c) =
      (∫ t in region, sourceDensity t) + ∑ c ∈ otherCells, cellIntegral c := by
  have hsplit :
      (∑ c ∈ otherCells, cellIntegral c) + (∑ c ∈ sourceCells, cellIntegral c) =
        ∑ c : FullCell, cellIntegral c :=
    Finset.sum_sdiff (Finset.subset_univ sourceCells)
  rw [sourceCells_integral_sum, ← region_integral_eq_sum_full87_cells] at hsplit
  exact hsplit.symm.trans (add_comm _ _)

end
end ImbalancedChen.P2Saving16Full87IntegralIdentity
