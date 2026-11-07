import ImbalancedChen.P2OriginalSaving16FourteenPhysicalAtlas
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Combination
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual original14 cell ownership, before any facet or simplex assertion.
The finite separator statement concerns the existing original literal
patterns. Its decision body is UNEVALUATED. Convex frontier nullity is a
proved Mathlib theorem, not an assumed wall or triangulation estimate.
This module does not claim within-cell simplex ownership or completeness.
-/
namespace ImbalancedChen.P2OriginalSaving16CellOwnership

noncomputable section
open Set MeasureTheory
open scoped BigOperators
open P2OriginalAscendingEighthCapDictionary
open P4AOriginalAscending14Literal42
open P2OriginalSaving16FourteenPhysicalAtlas

/-- Closed finite source statement on all fourteen actual assignments.
The empty mask is deliberately excluded, as in the physical old63 rows. -/
theorem literal_patterns_separated :
    ∀ c d : Cell, c ≠ d → ∃ I ∈ oldMasks,
      literalPattern (sourceId c) I ≠ literalPattern (sourceId d) I := by
  decide

theorem pairwise_disjoint_cells : Pairwise (Disjoint on cell) := by
  intro c d hcd
  apply Set.disjoint_left.2
  intro t hc hd
  obtain ⟨I, hI, hdiff⟩ := literal_patterns_separated c d hcd
  exact (sourceRows_cellGuard c t hc).incompatible_patterns
    (sourceRows_cellGuard d t hd) I hI hdiff

/-- The entire boundary of each actual96-row cell is null; the result
does not replace the cell by a candidate facet polytope. -/
theorem volume_frontier_cell (c : Cell) :
    (volume : Measure Point) (frontier (cell c)) = 0 :=
  (convex_cell c).addHaar_frontier volume

theorem closure_cell_ae_eq (c : Cell) :
    closure (cell c) =ᵐ[volume] cell c := by
  have hn : ∀ᵐ t ∂(volume : Measure Point), t ∉ frontier (cell c) :=
    by
      rw [ae_iff]
      simpa using volume_frontier_cell c
  filter_upwards [hn] with t ht
  change (t ∈ closure (cell c)) = (t ∈ cell c)
  apply propext
  constructor
  · intro hc
    by_contra hnot
    exact ht ⟨hc, by simpa only [(isOpen_cell c).interior_eq] using hnot⟩
  · exact subset_closure

theorem integral_closure_cell (c : Cell) :
    (∫ t in closure (cell c), sourceDensity t) =
      ∫ t in cell c, sourceDensity t :=
  setIntegral_congr_set (closure_cell_ae_eq c)

/-- Original fourteen-cell density, with no duplicate ownership and no
unproved geometric union or endpoint supplied as an argument. -/
theorem region_integral_eq_sum_cells :
    (∫ t in region, sourceDensity t) =
      ∑ c : Cell, ∫ t in cell c, sourceDensity t := by
  apply integral_iUnion_fintype (fun c => (isOpen_cell c).measurableSet)
    pairwise_disjoint_cells
  intro c
  exact integrableOn_sourceDensity_region.mono_set (subset_iUnion cell c)

theorem region_integral_eq_sum_closures :
    (∫ t in region, sourceDensity t) =
      ∑ c : Cell, ∫ t in closure (cell c), sourceDensity t := by
  rw [region_integral_eq_sum_cells]
  apply Finset.sum_congr rfl
  intro c _
  exact (integral_closure_cell c).symm

/-- Original weak physical rows, not candidate facets. -/
def closedRows (c : Cell) (t : Point) : Prop :=
  ∀ k : Fin 96, 0 ≤ evalRow (rows c k).2 t

theorem closure_cell_closedRows (c : Cell) {t : Point}
    (ht : t ∈ closure (cell c)) : closedRows c t := by
  intro k
  apply (closure_minimal (s := cell c)
    (t := {x | 0 ≤ evalRow (rows c k).2 x}) ?_
    (isClosed_le continuous_const (continuous_evalRow _))) ht
  intro x hx
  exact (hx k).le

/-- A genuine strict center and all original weak rows suffice for
closure membership. This helper is instantiated from original rational
centers by the data module; it assumes no polytope completeness. -/
theorem closedRows_mem_closure (c : Cell) (z : Point) (hz : sourceRows c z)
    {t : Point} (ht : closedRows c t) : t ∈ closure (cell c) := by
  let f : ℝ → Point := fun a => a • z + (1 - a) • t
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hpos : ∀ a ∈ Set.Ioo (0 : ℝ) 1, f a ∈ cell c := by
    intro a ha k
    rw [show f a = a • z + (1 - a) • t from rfl,
      evalRow_convexCombination _ _ _ _ _ (by ring)]
    exact add_pos_of_pos_of_nonneg (mul_pos ha.1 (hz k))
      (mul_nonneg (sub_nonneg.mpr ha.2.le) (ht k))
  have hzero : (0 : ℝ) ∈ closure (Set.Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact ⟨le_rfl, by norm_num⟩
  have hm : f 0 ∈ closure (f '' Set.Ioo (0 : ℝ) 1) :=
    image_closure_subset_closure_image hf ⟨0, hzero, rfl⟩
  have himage : f '' Set.Ioo (0 : ℝ) 1 ⊆ cell c := by
    rintro _ ⟨a, ha, rfl⟩
    exact hpos a ha
  simpa [f] using closure_mono himage hm

end
end ImbalancedChen.P2OriginalSaving16CellOwnership
