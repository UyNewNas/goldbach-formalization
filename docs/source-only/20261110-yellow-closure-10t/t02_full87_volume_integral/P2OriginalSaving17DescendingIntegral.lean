import ImbalancedChen.P2OriginalSaving17DescendingPulling

/-! SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
The actual stage17 Q96 endpoint lands on all fifteen original full87
descending Source integrals. Only a disjoint inner union is required;
there is no assertion of whole-cell vertex/triangulation coverage and no
archive/source integral lower hypothesis. Physical same-history equality
and the whole87 ordinary frontier are owned by T03, not this module.
-/
namespace ImbalancedChen.P2OriginalSaving17DescendingIntegral
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open P2OriginalDescendingEighthLogSemantics (Point)
open P2OriginalSaving17DescendingGeometry
open P2OriginalSaving17DescendingArchive
open P2OriginalSaving17DescendingSimplexBinding
open P2OriginalSaving17DescendingPulling
open P2OriginalSaving16JensenFloor (q96Floor)

def overlapSet (c : Fin 15) : Set Point :=
  ⋃ s : Fin (archive c).simplices.size, ⋃ t : Fin (archive c).simplices.size,
    if s = t then ∅ else rowSupport c s ∩ rowSupport c t
def exceptionalSet (c : Fin 15) : Set Point := frontier (cell c) ∪ overlapSet c
def ownedSupport (c : Fin 15) (s : Fin (archive c).simplices.size) : Set Point :=
  rowSupport c s \ exceptionalSet c

theorem overlapSet_null (c : Fin 15) : volume (overlapSet c) = 0 := by
  apply measure_iUnion_null
  intro s
  apply measure_iUnion_null
  intro t
  by_cases hst : s = t
  · simp [hst]
  · simp only [if_neg hst]
    exact original_within_cell_null_overlap c s t hst

theorem exceptionalSet_null (c : Fin 15) : volume (exceptionalSet c) = 0 :=
  measure_union_null (volume_frontier_cell c) (overlapSet_null c)

theorem exceptionalSet_measurable (c : Fin 15) : MeasurableSet (exceptionalSet c) := by
  apply isClosed_frontier.measurableSet.union
  apply MeasurableSet.iUnion
  intro s
  apply MeasurableSet.iUnion
  intro t
  by_cases hst : s = t
  · simp [hst]
  · simp only [if_neg hst]
    exact (rowSupport_measurable c s).inter (rowSupport_measurable c t)

theorem ownedSupport_measurable (c : Fin 15) (s : Fin (archive c).simplices.size) :
    MeasurableSet (ownedSupport c s) :=
  (rowSupport_measurable c s).diff (exceptionalSet_measurable c)

theorem ownedSupport_subset_cell (c : Fin 15) (s : Fin (archive c).simplices.size) :
    ownedSupport c s ⊆ cell c := by
  rintro x ⟨hx, hn⟩
  have hcl := rowSupport_subset_closure c s hx
  by_contra hnot
  apply hn
  left
  exact ⟨hcl, by simpa only [(isOpen_cell c).interior_eq] using hnot⟩

theorem ownedSupport_integrable (c : Fin 15) (s : Fin (archive c).simplices.size) :
    IntegrableOn sourceDensity (ownedSupport c s) :=
  (integrableOn_sourceDensity_cell c).mono_set (ownedSupport_subset_cell c s)

theorem ownedSupport_pairwise_disjoint (c : Fin 15) :
    Pairwise (fun s t : Fin (archive c).simplices.size =>
      Disjoint (ownedSupport c s) (ownedSupport c t)) := by
  intro s t hst
  apply Set.disjoint_left.mpr
  rintro x ⟨hxs, he⟩ ⟨hxt, _⟩
  apply he
  right
  apply mem_iUnion.mpr
  refine ⟨s, mem_iUnion.mpr ⟨t, ?_⟩⟩
  simpa only [if_neg hst] using And.intro hxs hxt

theorem ownedSupport_ae_eq (c : Fin 15) (s : Fin (archive c).simplices.size) :
    ownedSupport c s =ᵐ[volume] rowSupport c s := by
  have hn : ∀ᵐ x : Point ∂volume, x ∉ exceptionalSet c := by
    rw [ae_iff]
    simpa only [not_not] using exceptionalSet_null c
  filter_upwards [hn] with x hx
  simp [ownedSupport, hx]

theorem ownedSupport_integral (c : Fin 15) (s : Fin (archive c).simplices.size) :
    (∫ x in ownedSupport c s, sourceDensity x) =
      ∫ x in rowSupport c s, sourceDensity x :=
  setIntegral_congr_set (ownedSupport_ae_eq c s)

def ownedUnion (c : Fin 15) : Set Point := ⋃ s : Fin (archive c).simplices.size, ownedSupport c s
theorem ownedUnion_subset_cell (c : Fin 15) : ownedUnion c ⊆ cell c := by
  intro x hx
  obtain ⟨s, hs⟩ := mem_iUnion.mp hx
  exact ownedSupport_subset_cell c s hs

theorem ownedUnion_integral (c : Fin 15) :
    (∫ x in ownedUnion c, sourceDensity x) =
      ∑ s : Fin (archive c).simplices.size, ∫ x in rowSupport c s, sourceDensity x := by
  rw [ownedUnion, integral_iUnion_fintype (ownedSupport_measurable c)
    (ownedSupport_pairwise_disjoint c) (ownedSupport_integrable c)]
  simp_rw [ownedSupport_integral]

theorem original_simplex_integral_sum_le_cell_integral (c : Fin 15) :
    (∑ s : Fin (archive c).simplices.size, ∫ x in rowSupport c s, sourceDensity x) ≤
      ∫ x in cell c, sourceDensity x := by
  rw [← ownedUnion_integral]
  apply setIntegral_mono_set (integrableOn_sourceDensity_cell c)
  · filter_upwards [ae_restrict_mem (isOpen_cell c).measurableSet] with x hx
    exact sourceDensity_nonneg_on_cell hx
  · exact Filter.Eventually.of_forall (fun x hx => ownedUnion_subset_cell c hx)

theorem original_cell_floor_le_cell_integral (c : Fin 15) :
    (cellFloorNumerator c : ℝ) / (2 : ℝ) ^ 96 ≤ ∫ x in cell c, sourceDensity x := by
  have he : (cellFloorNumerator c : ℝ) / (2 : ℝ) ^ 96 =
      ∑ s : Fin (archive c).simplices.size,
        (q96Floor (jensenQ (rowVertices c s)) : ℝ) / (2 : ℝ) ^ 96 := by
    simp [cellFloorNumerator, rowVertices, Finset.sum_div]
  rw [he]
  exact (Finset.sum_le_sum (fun s _ => original_row_q96 c s)).trans
    (original_simplex_integral_sum_le_cell_integral c)

/-- The per-cell endpoint is attached to the ACTUAL full87 Source and
its unaltered ideal eighth kernel, not just an unowned simplex sum. -/
theorem original_cell_floor_le_full87_source_integral (c : Fin 15) :
    (cellFloorNumerator c : ℝ) / (2 : ℝ) ^ 96 ≤
      ∫ t in P4AOriginalFull87StrictActionTrim.sourceSet (.descending c),
        P4AOriginalFull87EighthKernelControl.kernel (.descending c) t := by
  simp_rw [← sourceDensity_eq_kernel c]
  rw [← cell_eq_original_source c]
  exact original_cell_floor_le_cell_integral c

/-- Whole original stage17: 63,612 separate outward floors, fifteen real
Source integrals, original coefficient four and ordinary Lebesgue volume.
There is no remaining geometric, moment, integral or floor hypothesis. -/
theorem original_stage17_floor_le_sum_full87_integrals :
    (467454156274267811817033 : ℝ) / (2 : ℝ) ^ 96 ≤
      ∑ c : Fin 15,
        ∫ t in P4AOriginalFull87StrictActionTrim.sourceSet (.descending c),
          P4AOriginalFull87EighthKernelControl.kernel (.descending c) t := by
  rw [← original_q96_aggregate_real]
  exact Finset.sum_le_sum (fun c _ => original_cell_floor_le_full87_source_integral c)

end
end ImbalancedChen.P2OriginalSaving17DescendingIntegral
