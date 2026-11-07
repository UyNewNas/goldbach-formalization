import ImbalancedChen.P2OriginalSaving16PullingOwnership
import Mathlib.Data.Fintype.BigOperators

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT. Inherited K canonical
moment HOLD and every J/M source-only HOLD remain. Finite bodies remain
UNEVALUATED. This is a legal inner-union argument for the exact original
fourteen cells and39741 supports, with no whole-cell coverage requirement.
-/
namespace ImbalancedChen.P2OriginalSaving16OwnedIntegral

noncomputable section
open Set MeasureTheory
open scoped BigOperators
open P2OriginalAscendingEighthCapDictionary
open P2OriginalSaving16FourteenPhysicalAtlas
open P2OriginalSaving16CellOwnership
open P2OriginalSaving16OriginalArchive
open P2OriginalSaving16SimplexBinding
open P2OriginalSaving16PullingOwnership

/-- Small original index dictionary; this does not inspect a witness. -/
theorem atlasCell_injective : Function.Injective atlasCell := by
  have hid : Function.Injective originalId := by decide
  intro c d h
  apply hid
  have he := congrArg (fun a : Cell => (sourceId a).val) h
  simpa only [atlasCell_sourceId] using he

def overlapSet (c : Fin 14) : Set Point :=
  ⋃ s : Fin (archive c).simplices.size, ⋃ t : Fin (archive c).simplices.size,
    if s = t then ∅ else rowSupport c s ∩ rowSupport c t

def exceptionalSet (c : Fin 14) : Set Point :=
  frontier (cell (atlasCell c)) ∪ overlapSet c

def ownedSupport (r : RowIndex) : Set Point :=
  rowSupport r.1 r.2 \ exceptionalSet r.1

theorem overlapSet_null (c : Fin 14) : volume (overlapSet c) = 0 := by
  apply measure_iUnion_null
  intro s
  apply measure_iUnion_null
  intro t
  by_cases hst : s = t
  · simp [hst]
  · simp only [if_neg hst]
    exact original_within_cell_null_overlap c s t hst

theorem exceptionalSet_null (c : Fin 14) : volume (exceptionalSet c) = 0 :=
  measure_union_null (volume_frontier_cell (atlasCell c)) (overlapSet_null c)

theorem exceptionalSet_measurable (c : Fin 14) : MeasurableSet (exceptionalSet c) := by
  apply isClosed_frontier.measurableSet.union
  apply MeasurableSet.iUnion
  intro s
  apply MeasurableSet.iUnion
  intro t
  by_cases hst : s = t
  · simp [hst]
  · simp only [if_neg hst]
    exact (rowSupport_measurable c s).inter (rowSupport_measurable c t)

theorem ownedSupport_measurable (r : RowIndex) : MeasurableSet (ownedSupport r) :=
  (rowSupport_measurable r.1 r.2).diff (exceptionalSet_measurable r.1)

/-- M proved each ORIGINAL simplex lies in the correct cell closure.
Removing that cell's null frontier makes the inclusion strict. -/
theorem ownedSupport_subset_cell (r : RowIndex) :
    ownedSupport r ⊆ cell (atlasCell r.1) := by
  rintro x ⟨hx, hn⟩
  have hcl := rowSupport_subset_closure r.1 r.2 hx
  by_contra hnot
  apply hn
  left
  exact ⟨hcl, by simpa only [(isOpen_cell (atlasCell r.1)).interior_eq] using hnot⟩

theorem ownedSupport_subset_region (r : RowIndex) : ownedSupport r ⊆ region :=
  (ownedSupport_subset_cell r).trans (subset_iUnion cell (atlasCell r.1))

theorem ownedSupport_integrable (r : RowIndex) :
    IntegrableOn sourceDensity (ownedSupport r) :=
  integrableOn_sourceDensity_region.mono_set (ownedSupport_subset_region r)

theorem ownedSupport_same_cell_disjoint (c : Fin 14)
    (s t : Fin (archive c).simplices.size) (hst : s ≠ t) :
    Disjoint (ownedSupport ⟨c, s⟩) (ownedSupport ⟨c, t⟩) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨hxs, he⟩ ⟨hxt, _⟩
  apply he
  right
  apply mem_iUnion.mpr
  refine ⟨s, mem_iUnion.mpr ⟨t, ?_⟩⟩
  simpa only [if_neg hst] using And.intro hxs hxt

theorem ownedSupport_pairwise_disjoint :
    Pairwise (fun r s : RowIndex => Disjoint (ownedSupport r) (ownedSupport s)) := by
  rintro ⟨c, s⟩ ⟨d, t⟩ hne
  by_cases hcd : c = d
  · subst d
    exact ownedSupport_same_cell_disjoint c s t
      (fun hst => hne (by cases hst; rfl))
  · have hcells : atlasCell c ≠ atlasCell d := fun he => hcd (atlasCell_injective he)
    exact (pairwise_disjoint_cells hcells).mono
      (ownedSupport_subset_cell ⟨c, s⟩) (ownedSupport_subset_cell ⟨d, t⟩)

theorem ownedSupport_ae_eq (r : RowIndex) :
    ownedSupport r =ᵐ[volume] rowSupport r.1 r.2 := by
  have hn : ∀ᵐ x : Point ∂volume, x ∉ exceptionalSet r.1 := by
    rw [ae_iff]
    simpa only [not_not] using exceptionalSet_null r.1
  filter_upwards [hn] with x hx
  simp [ownedSupport, hx]

theorem ownedSupport_integral (r : RowIndex) :
    (∫ x in ownedSupport r, sourceDensity x) =
      ∫ x in rowSupport r.1 r.2, sourceDensity x :=
  setIntegral_congr_set (ownedSupport_ae_eq r)

def ownedUnion : Set Point := ⋃ r : RowIndex, ownedSupport r

theorem ownedUnion_subset_region : ownedUnion ⊆ region := by
  intro x hx
  obtain ⟨r, hr⟩ := mem_iUnion.mp hx
  exact ownedSupport_subset_region r hr

/-- Ordinary finite integral additivity is applied only after the
geometrically proved null intersections have been removed. -/
theorem ownedUnion_integral :
    (∫ x in ownedUnion, sourceDensity x) =
      ∑ c : Fin 14, ∑ s : Fin (archive c).simplices.size,
        ∫ x in rowSupport c s, sourceDensity x := by
  rw [ownedUnion, integral_iUnion_fintype ownedSupport_measurable
    ownedSupport_pairwise_disjoint ownedSupport_integrable]
  simp_rw [ownedSupport_integral]
  exact Fintype.sum_sigma _

/-- No source inclusion, disjointness, coverage, integral estimate, or
endpoint is an argument. All39741 actual supports occur exactly once. -/
theorem original_simplex_integral_sum_le_source_integral :
    (∑ c : Fin 14, ∑ s : Fin (archive c).simplices.size,
      ∫ x in rowSupport c s, sourceDensity x) ≤
        ∫ x in region, sourceDensity x := by
  rw [← ownedUnion_integral]
  apply setIntegral_mono_set integrableOn_sourceDensity_region
  · filter_upwards [ae_restrict_mem measurableSet_region] with x hx
    exact (sourceDensity_pos_on_region hx).le
  · exact Filter.Eventually.of_forall ownedUnion_subset_region

/-- The original M Jensen/Q96 endpoint now lands on its original14
source integral. Arithmetic weak-face payment and common causal history
remain different tasks; no final current-K theorem is claimed here. -/
theorem historical_endpoint_le_source_integral :
    (1222997719565324892497827 : ℝ) / (2 : ℝ) ^ 96 ≤
      ∫ x in region, sourceDensity x :=
  historical_endpoint_le_sum_simplex_integrals.trans
    original_simplex_integral_sum_le_source_integral

end
end ImbalancedChen.P2OriginalSaving16OwnedIntegral
