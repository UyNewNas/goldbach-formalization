import ImbalancedChen.P2OriginalSaving19PullingOwnership
import ImbalancedChen.P2OriginalSaving19Original28918FloorBinding

/-!
SOURCE ONLY / UNCOMPILED / ZERO CREDIT. All predecessor HOLDs persist.
The actual ORIGINAL13/28918 sum is embedded in J.selectedSaving by deleting
null source walls and within-cell overlaps. Different strict cells are
already disjoint by their original branch choices. A legal inner union
suffices for this positive lower saving; no coverage is claimed or assumed.
The floor is a replacement for the same original rows, not a second gain.
-/
namespace ImbalancedChen.P2OriginalSaving19OwnedIntegral

noncomputable section
open Set MeasureTheory
open scoped BigOperators
open P2OriginalThirdMinorantLogDictionarySourceOnly
open P2OriginalSaving19SimplexMoments
open P2OriginalSaving19MomentFloorConsumer
open P2OriginalSaving19Archive
open P2OriginalSaving19Original28918
open P2OriginalSaving19Original28918FloorBinding
open P2OriginalSaving19OwnedSource
open P2OriginalSaving19PullingOwnership
open OriginalAscendingThirteenCellOwnership
open P2OriginalSaving19SourceMeasure

def overlapSet (c : Fin 13) : Set Point :=
  ⋃ i : CellRow c, ⋃ j : CellRow c,
    if i = j then ∅ else actualSupport ⟨c, i⟩ ∩ actualSupport ⟨c, j⟩

def exceptionalSet (c : Fin 13) : Set Point := sourceWalls c ∪ overlapSet c

def legalOwnedSupport (r : OriginalRowIndex) : Set Point :=
  actualSupport r \ exceptionalSet r.1

theorem overlapSet_null (c : Fin 13) : volume (overlapSet c) = 0 := by
  apply measure_iUnion_null
  intro i
  apply measure_iUnion_null
  intro j
  by_cases h : i = j
  · simp [h]
  · simp only [if_neg h]
    exact original_within_cell_null_overlap c i j h

theorem exceptionalSet_null (c : Fin 13) : volume (exceptionalSet c) = 0 :=
  measure_union_null (sourceWalls_null c) (overlapSet_null c)

theorem exceptionalSet_measurable (c : Fin 13) : MeasurableSet (exceptionalSet c) := by
  apply (sourceWalls_measurable c).union
  apply MeasurableSet.iUnion
  intro i
  apply MeasurableSet.iUnion
  intro j
  by_cases h : i = j
  · simp [h]
  · simp only [if_neg h]
    exact (actualSupport_measurable ⟨c, i⟩).inter (actualSupport_measurable ⟨c, j⟩)

theorem legalOwnedSupport_measurable (r : OriginalRowIndex) :
    MeasurableSet (legalOwnedSupport r) :=
  (actualSupport_measurable r).diff (exceptionalSet_measurable r.1)

theorem legalOwnedSupport_subset_cell (r : OriginalRowIndex) :
    legalOwnedSupport r ⊆ cell r.1 := by
  rintro x ⟨hx, he⟩
  exact support_off_walls_in_cell r ⟨hx, fun hw => he (Or.inl hw)⟩

theorem legalOwnedSupport_integrable (r : OriginalRowIndex) :
    IntegrableOn conservativeDensity (legalOwnedSupport r) :=
  (cell_density_integrable r.1).mono_set (legalOwnedSupport_subset_cell r)

theorem legalOwnedSupport_cell_disjoint (c : Fin 13) (i j : CellRow c) (hij : i ≠ j) :
    Disjoint (legalOwnedSupport ⟨c, i⟩) (legalOwnedSupport ⟨c, j⟩) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨hi, he⟩ ⟨hj, _⟩
  apply he
  right
  apply mem_iUnion.mpr
  refine ⟨i, mem_iUnion.mpr ⟨j, ?_⟩⟩
  simpa only [if_neg hij] using And.intro hi hj

theorem legalOwnedSupport_pairwise_disjoint :
    Pairwise (fun r s : OriginalRowIndex => Disjoint (legalOwnedSupport r) (legalOwnedSupport s)) := by
  rintro ⟨c, i⟩ ⟨d, j⟩ hrs
  by_cases hcd : c = d
  · subst d
    exact legalOwnedSupport_cell_disjoint c i j
      (fun hij => hrs (by cases hij; rfl))
  · exact (strict_cells_disjoint hcd).mono
      (legalOwnedSupport_subset_cell ⟨c, i⟩) (legalOwnedSupport_subset_cell ⟨d, j⟩)

theorem legalOwnedSupport_ae_eq (r : OriginalRowIndex) :
    legalOwnedSupport r =ᵐ[volume] actualSupport r := by
  have he : ∀ᵐ x : Point ∂volume, x ∉ exceptionalSet r.1 := by
    rw [ae_iff]
    simpa only [not_not] using exceptionalSet_null r.1
  filter_upwards [he] with x hx
  simp [legalOwnedSupport, hx]

theorem legalOwnedSupport_integral (r : OriginalRowIndex) :
    (∫ x in legalOwnedSupport r, conservativeDensity x) =
      ∫ x in support (rowLinear r) (rowBase r), conservativeDensity x :=
  setIntegral_congr_set (legalOwnedSupport_ae_eq r)

def legalSelectedSource : Set Point := ⋃ r : OriginalRowIndex, legalOwnedSupport r

theorem legalSelectedSource_subset_selected : legalSelectedSource ⊆ selectedSource := by
  intro x hx
  obtain ⟨r, hr⟩ := mem_iUnion.mp hx
  exact mem_iUnion.mpr ⟨r.1, legalOwnedSupport_subset_cell r hr⟩

theorem legalSelectedSource_integral :
    (∫ x in legalSelectedSource, conservativeDensity x) =
      ∑ r : OriginalRowIndex,
        ∫ x in support (rowLinear r) (rowBase r), conservativeDensity x := by
  rw [legalSelectedSource, integral_iUnion_fintype legalOwnedSupport_measurable
    legalOwnedSupport_pairwise_disjoint legalOwnedSupport_integrable]
  exact Finset.sum_congr rfl (fun r _ => legalOwnedSupport_integral r)

/-- Actual original28918 row integrals, with no assumed inclusion,
disjointness, coverage, integral estimate or replacement source identity. -/
theorem original_simplex_integral_sum_le_selectedSaving :
    (∑ r : OriginalRowIndex,
      ∫ x in support (rowLinear r) (rowBase r), conservativeDensity x) ≤ selectedSaving := by
  rw [← legalSelectedSource_integral]
  apply setIntegral_mono_set selectedSource_density_integrable
  · filter_upwards [ae_restrict_mem selectedSource_measurable] with x hx
    obtain ⟨c, hc⟩ := mem_iUnion.mp hx
    exact cell_density_nonneg hc
  · exact Filter.Eventually.of_forall legalSelectedSource_subset_selected

/-- The already-established K row floors and M actual higher-moment
binding now land on the same original J.selectedSaving, exactly once. -/
theorem original_row_floor_sum_le_selectedSaving :
    (∑ r : OriginalRowIndex, (originalRowFloor (fullMomentRow r) : ℝ)) ≤ selectedSaving :=
  (original_family_floor_sum_le_integral_sum fullMomentRow).trans
    original_simplex_integral_sum_le_selectedSaving

theorem original_saved_Q96_sum_le_selectedSaving :
    (∑ r : OriginalRowIndex,
      ((((rawMomentRow r).newFloorQ96 : ℚ) / (2 : ℚ)^96) : ℝ)) ≤ selectedSaving := by
  simp_rw [saved_Q96_binding]
  exact original_row_floor_sum_le_selectedSaving

/-- Local analytic endpoint only; common historical finite caps, source
count/mean compilation, all22/current-c closure remain separate OPEN work. -/
theorem original_endpoint_le_selectedSaving :
    (283388722705335806564439 : ℝ) / (2 : ℝ)^96 ≤ selectedSaving :=
  original_endpoint_le_simplex_integral_sum.trans original_simplex_integral_sum_le_selectedSaving

end
end ImbalancedChen.P2OriginalSaving19OwnedIntegral
