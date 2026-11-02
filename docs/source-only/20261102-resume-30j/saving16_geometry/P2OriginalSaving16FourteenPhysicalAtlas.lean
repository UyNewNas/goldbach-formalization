import ImbalancedChen.P4AOriginalRemainingAscendingAtlas
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The fourteen saving16 cells are the original ascending cells 0,...,14
except7. The existing cell0, cell1, cell2 and remaining-eleven literal
decoders supply their actual 96 physical rows. This file copies no row
payload, substitutes no sixth-policy family and imports no T10 simplex.

The new analytic content is a common closed positive-denominator carrier
for the ENTIRE fourteen-cell union and its closure. It proves continuity,
uniform boundedness and integrability of the actual coefficient-4 residual
kernel, without an integrability or enclosure premise. All eight original
coordinates and both residual denominator factors stay uniformly positive
on this closure. This does not identify a candidate facet polytope with a
cell, certify its triangulation, or prove the historical Q96 endpoint.
-/

namespace ImbalancedChen.P2OriginalSaving16FourteenPhysicalAtlas

noncomputable section
open scoped Classical BigOperators
open Set MeasureTheory VariableEnvelope
open P2OriginalAscendingEighthCapDictionary
open P4AOriginalAscending14Literal42

/-- Three earlier decoded cells plus the eleven remaining saving16 cells.
The right summand is a family of eighth cells, not eleven sixth actions. -/
abbrev Cell := Fin 3 ⊕ P4AOriginalRemainingAscendingAtlas.RemainingCell

def sourceId : Cell → Fin 15
  | .inl i => i.castLE (by omega)
  | .inr i => P4AOriginalRemainingAscendingAtlas.sourceId i

/-- Reuse the frozen original rational row tables without a new export. -/
def rows : Cell → Fin 96 → String × (Fin 9 → ℚ)
  | .inl i => if i = 0 then P4AOriginalAscendingCell0Literal96.rows
      else if i = 1 then P4AOriginalAscendingCell1Affine.rows1
      else P4AOriginalAscendingCell2Affine.rows2
  | .inr i => P4AOriginalRemainingAscendingAtlas.rows i

abbrev evalRow := P4AOriginalSeed7Unequal15Literal.evalAffine

def sourceRows (c : Cell) (t : Point) : Prop :=
  ∀ k : Fin 96, 0 < evalRow (rows c k).2 t

def cell (c : Cell) : Set Point := {t | sourceRows c t}

def region : Set Point := ⋃ c : Cell, cell c

theorem card_cell : Fintype.card Cell = 14 := by
  norm_num [Cell, P4AOriginalRemainingAscendingAtlas.RemainingCell]

theorem sourceId_selected (c : Cell) : sourceId c ∈ selectedCellIndices := by
  cases c with
  | inl i =>
      apply (mem_selectedCellIndices _).2
      intro h
      have hv := congrArg Fin.val h
      have hi := i.isLt
      change i.val = 7 at hv
      omega
  | inr i => exact P4AOriginalRemainingAscendingAtlas.sourceId_selected i

/-- No cell index in saving16 is lost by the three-plus-eleven presentation.
This small index identity does not decide any affine/geometry certificate. -/
theorem sourceId_surjective_selected (i : Fin 15) (hi : i ∈ selectedCellIndices) :
    ∃ c : Cell, sourceId c = i := by
  have hi7 := (mem_selectedCellIndices i).mp hi
  fin_cases i
  · exact ⟨.inl 0, rfl⟩
  · exact ⟨.inl 1, rfl⟩
  · exact ⟨.inl 2, rfl⟩
  · exact ⟨.inr 0, rfl⟩
  · exact ⟨.inr 1, rfl⟩
  · exact ⟨.inr 2, rfl⟩
  · exact ⟨.inr 3, rfl⟩
  · exact (hi7 rfl).elim
  · exact ⟨.inr 4, rfl⟩
  · exact ⟨.inr 5, rfl⟩
  · exact ⟨.inr 6, rfl⟩
  · exact ⟨.inr 7, rfl⟩
  · exact ⟨.inr 8, rfl⟩
  · exact ⟨.inr 9, rfl⟩
  · exact ⟨.inr 10, rfl⟩

private theorem remainingId_ge_three
    (i : P4AOriginalRemainingAscendingAtlas.RemainingCell) :
    3 ≤ (P4AOriginalRemainingAscendingAtlas.sourceId i).val := by
  fin_cases i <;> norm_num [P4AOriginalRemainingAscendingAtlas.sourceId]

theorem sourceId_injective : Function.Injective sourceId := by
  intro c d h
  cases c with
  | inl i =>
      cases d with
      | inl j =>
          apply congrArg Sum.inl
          apply Fin.ext
          exact congrArg Fin.val h
      | inr j =>
          have heq := congrArg Fin.val h
          have hj := remainingId_ge_three j
          have hi := i.isLt
          change i.val = (P4AOriginalRemainingAscendingAtlas.sourceId j).val at heq
          omega
  | inr i =>
      cases d with
      | inl j =>
          have heq := congrArg Fin.val h
          have hi := remainingId_ge_three i
          have hj := j.isLt
          change (P4AOriginalRemainingAscendingAtlas.sourceId i).val = j.val at heq
          omega
      | inr j =>
          exact congrArg Sum.inr (P4AOriginalRemainingAscendingAtlas.sourceId_injective h)

theorem continuous_evalRow (a : Fin 9 → ℚ) :
    Continuous (fun t : Point => evalRow a t) := by
  unfold evalRow P4AOriginalSeed7Unequal15Literal.evalAffine
  fun_prop

theorem isOpen_cell (c : Cell) : IsOpen (cell c) := by
  have heq : cell c = ⋂ k : Fin 96, {t : Point | 0 < evalRow (rows c k).2 t} := by
    ext t
    simp [cell, sourceRows]
  rw [heq]
  exact isOpen_iInter_of_finite (fun k =>
    isOpen_lt continuous_const (continuous_evalRow (rows c k).2))

theorem isOpen_region : IsOpen region := isOpen_iUnion isOpen_cell

theorem measurableSet_region : MeasurableSet region := isOpen_region.measurableSet

theorem evalRow_convexCombination (row : Fin 9 → ℚ) (x y : Point)
    (a b : ℝ) (hab : a + b = 1) :
    evalRow row (a • x + b • y) = a * evalRow row x + b * evalRow row y := by
  norm_num [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
    Fin.sum_univ_succ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination -(row 0 : ℝ) * hab

/-- Convexity follows from every actual rational row, without candidate
facets, LP output, strict-center witnesses or hull reconstruction. -/
theorem convex_cell (c : Cell) : Convex ℝ (cell c) := by
  intro x hx y hy a b ha hb hab
  intro k
  rw [evalRow_convexCombination _ x y a b hab]
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    simpa only [ha0, hb1, zero_mul, zero_add, one_mul] using hy k
  · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    exact add_pos_of_pos_of_nonneg (mul_pos hapos (hx k)) (mul_nonneg hb (hy k).le)

/-- Each original decoder supplies its OWN branch pattern and full guard.
In particular we do not infer cell1/2 or a remaining cell from cell0's
incompatible old-plane inequalities. -/
theorem sourceRows_cellGuard (c : Cell) (t : Point) (h : sourceRows c t) :
    CellGuard (literalPattern (sourceId c)) t := by
  cases c with
  | inl i =>
      fin_cases i
      · exact P4AOriginalCell0AffineChronology.literalRows_cellGuard t
          (by simpa [sourceRows, rows] using h)
      · exact P4AOriginalAscendingCell1Affine.literalRows_cellGuard t
          (by simpa [sourceRows, rows] using h)
      · exact P4AOriginalAscendingCell2Affine.literalRows_cellGuard t
          (by simpa [sourceRows, rows] using h)
  | inr i =>
      exact P4AOriginalRemainingAscendingAtlas.sourceRows_cellGuard i t h

theorem region_selectedFamilyGuard {t : Point} (ht : t ∈ region) :
    SelectedFamilyGuard literalPattern t := by
  obtain ⟨c, hc⟩ := mem_iUnion.mp ht
  exact ⟨sourceId c, sourceId_selected c, sourceRows_cellGuard c t hc⟩

/-- Frozen interface for a compiler working on any compact subset of the
actual whole fourteen-cell source. The branch map is the original map. -/
theorem subset_selectedFamilyGuard {K : Set Point} (hK : K ⊆ region) :
    K ⊆ {t | SelectedFamilyGuard literalPattern t} :=
  fun _ ht => region_selectedFamilyGuard (hK ht)

theorem sourceRows_original_envelopes (c : Cell) (t : Point) (h : sourceRows c t) :
    rawSixthEnvelope t = R t ∧ VariableEnvelope.original (t 0) (t 1) (t 2) = R t := by
  have hg := sourceRows_cellGuard c t h
  exact ⟨hg.rawSixth_eq, hg.originalThird_eq⟩

/-- The physical subset is {1,8} in one-based notation, with exactly the
same six unselected squares and buffered tent licence in every cell. -/
theorem sourceRows_mask129_support (c : Cell) (t : Point) (h : sourceRows c t) :
    (∀ j, fullSquare t j < M t) ∧
    (∀ j : Fin 8, 0 < j → j < 7 → selectedRemainingSquare t j < M t) ∧
    M t < v (∑ i ∈ selected129, t i) := by
  have hg := sourceRows_cellGuard c t h
  exact ⟨hg.full_squares, hg.selected_squares, new_cap_strict_license t⟩

/-- The true inherited sixth exponent stays a separate input to this
geometric theorem. The seventh history, not R alone, supplies its lower
residual endpoint. -/
theorem sourceRows_inherited_residual_range (c : Cell) (t : Point)
    (h : sourceRows c t) (current : ℝ) (hc : CurrentParentGuard t current) :
    0 < t 7 ∧ t 7 < current - S t ∧ current - S t ≤ 3 * t 7 ∧
      t 7 < M t - S t ∧ M t - S t ≤ 3 * t 7 :=
  residual_parameter_range (sourceRows_cellGuard c t h) current hc

def cutoff : ℝ := 53 / 13824

theorem cutoff_pos : 0 < cutoff := by norm_num [cutoff]

/-- A closed rectangular box, with the original cutoff retained. -/
def coordinateBox : Set Point := Set.univ.pi (fun _ => Set.Icc cutoff mu)

/-- This is an analytic containing set, NOT a substitute adopted cell.
The integral remains restricted to the actual literal source union. -/
def safeCarrier : Set Point :=
  coordinateBox ∩
    ({t | cutoff ≤ R t - S t} ∩ {t | cutoff ≤ M t - S t})

theorem continuous_R : Continuous R := by
  unfold R d C
  fun_prop

theorem continuous_M : Continuous M := by
  unfold M selectedSum A C eta
  fun_prop

theorem continuous_S : Continuous S := by
  unfold S
  exact continuous_finset_sum _ (fun i _ => continuous_apply i)

theorem continuous_fullSquare (j : Fin 8) : Continuous (fun t => fullSquare t j) := by
  unfold fullSquare prefixSum
  fun_prop

theorem continuous_selectedRemainingSquare (j : Fin 8) :
    Continuous (fun t => selectedRemainingSquare t j) := by
  unfold selectedRemainingSquare selectedSum
  fun_prop

theorem isCompact_coordinateBox : IsCompact coordinateBox :=
  isCompact_univ_pi (fun _ => isCompact_Icc)

theorem isClosed_safeCarrier : IsClosed safeCarrier :=
  isCompact_coordinateBox.isClosed.inter
    ((isClosed_le continuous_const (continuous_R.sub continuous_S)).inter
      (isClosed_le continuous_const (continuous_M.sub continuous_S)))

theorem isCompact_safeCarrier : IsCompact safeCarrier :=
  isCompact_coordinateBox.of_isClosed_subset isClosed_safeCarrier inter_subset_left

/-- The complete original order and compact-cutoff rows force every
coordinate into the same positive interval, without a vertex premise. -/
theorem sourceRows_coordinate_bounds (c : Cell) (t : Point) (h : sourceRows c t) :
    ∀ j, cutoff < t j ∧ t j < mu := by
  have hg := sourceRows_cellGuard c t h
  intro j
  constructor
  · by_cases hj : j = 7
    · simpa [hj, cutoff] using hg.compact_cutoff
    · exact hg.compact_cutoff.trans (hg.order (by omega : j < 7))
  · by_cases hj : j = 0
    · simpa [hj] using hg.largest
    · exact (hg.order (by omega : 0 < j)).trans hg.largest

/-- All ten denominator factors have a uniform lower endpoint on the
whole open cell. No simplex extrema or numerical replay is used. -/
theorem sourceRows_denominator_floors (c : Cell) (t : Point) (h : sourceRows c t) :
    cutoff < R t - S t ∧ cutoff < M t - S t ∧ ∀ j, cutoff < t j := by
  have hg := sourceRows_cellGuard c t h
  have hcoord := sourceRows_coordinate_bounds c t h
  refine ⟨?_, ?_, fun j => (hcoord j).1⟩
  · linarith [hg.old_residual, (hcoord 7).1]
  · linarith [hg.old_residual, hg.improvement, (hcoord 7).1]

theorem cell_subset_safeCarrier (c : Cell) : cell c ⊆ safeCarrier := by
  intro t ht
  have hcoords := sourceRows_coordinate_bounds c t ht
  have hden := sourceRows_denominator_floors c t ht
  exact ⟨fun j _ => ⟨(hcoords j).1.le, (hcoords j).2.le⟩,
    hden.1.le, hden.2.1.le⟩

theorem region_subset_safeCarrier : region ⊆ safeCarrier := by
  intro t ht
  obtain ⟨c, hc⟩ := mem_iUnion.mp ht
  exact cell_subset_safeCarrier c hc

theorem closure_cell_subset_safeCarrier (c : Cell) : closure (cell c) ⊆ safeCarrier :=
  closure_minimal (cell_subset_safeCarrier c) isClosed_safeCarrier

theorem isCompact_closure_cell (c : Cell) : IsCompact (closure (cell c)) :=
  isCompact_safeCarrier.of_isClosed_subset isClosed_closure (closure_cell_subset_safeCarrier c)

theorem closure_region_subset_safeCarrier : closure region ⊆ safeCarrier :=
  closure_minimal region_subset_safeCarrier isClosed_safeCarrier

theorem isCompact_closure_region : IsCompact (closure region) :=
  isCompact_safeCarrier.of_isClosed_subset isClosed_closure closure_region_subset_safeCarrier

theorem closure_region_denominator_floors {t : Point} (ht : t ∈ closure region) :
    cutoff ≤ R t - S t ∧ cutoff ≤ M t - S t ∧ ∀ j, cutoff ≤ t j := by
  have hs := closure_region_subset_safeCarrier ht
  exact ⟨hs.2.1, hs.2.2, fun j => (hs.1 j (mem_univ j)).1⟩

/-- Continuous full/selected support inequalities survive on the actual
closure as weak inequalities. Boundary histories are not activated. -/
theorem closure_region_support {t : Point} (ht : t ∈ closure region) :
    (∀ j, fullSquare t j ≤ M t) ∧
    (∀ j : Fin 8, 0 < j → j < 7 → selectedRemainingSquare t j ≤ M t) := by
  constructor
  · intro j
    apply (closure_minimal (s := region)
      (t := {x | fullSquare x j ≤ M x}) ?_
      (isClosed_le (continuous_fullSquare j) continuous_M)) ht
    intro x hx
    obtain ⟨c, hc⟩ := mem_iUnion.mp hx
    exact ((sourceRows_cellGuard c x hc).full_squares j).le
  · intro j hj0 hj7
    apply (closure_minimal (s := region)
      (t := {x | selectedRemainingSquare x j ≤ M x}) ?_
      (isClosed_le (continuous_selectedRemainingSquare j) continuous_M)) ht
    intro x hx
    obtain ⟨c, hc⟩ := mem_iUnion.mp hx
    exact ((sourceRows_cellGuard c x hc).selected_squares j hj0 hj7).le

theorem continuous_denominator :
    Continuous (fun t : Point => (R t - S t) * (M t - S t) * ∏ i, t i) := by
  apply ((continuous_R.sub continuous_S).mul (continuous_M.sub continuous_S)).mul
  exact continuous_finsetProd _ (fun i _ => continuous_apply i)

theorem safeCarrier_denominator_pos {t : Point} (ht : t ∈ safeCarrier) :
    0 < (R t - S t) * (M t - S t) * ∏ i, t i := by
  have hR := cutoff_pos.trans_le ht.2.1
  have hM := cutoff_pos.trans_le ht.2.2
  have hi (i : Fin 8) : 0 < t i := cutoff_pos.trans_le (ht.1 i (mem_univ i)).1
  exact mul_pos (mul_pos hR hM) (Finset.prod_pos (fun i _ => hi i))

/-- The exact manuscript kernel, coefficient4 and ordered-coordinate
product included, is continuous on the proved containing compact set. -/
theorem continuousOn_sourceDensity : ContinuousOn sourceDensity safeCarrier := by
  apply (continuous_const.mul (continuous_M.sub continuous_R)).continuousOn.div
    continuous_denominator.continuousOn
  intro t ht
  exact (safeCarrier_denominator_pos ht).ne'

/-- A genuine uniform bound follows from the actual gate-derived carrier;
the caller supplies neither a kernel bound nor a geometry certificate. -/
theorem sourceDensity_uniformly_bounded :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ closure region, ‖sourceDensity t‖ ≤ C := by
  obtain ⟨B, hB⟩ :=
    (isCompact_safeCarrier.image_of_continuousOn continuousOn_sourceDensity).isBounded.exists_norm_le
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro t ht
  exact (hB _ ⟨t, closure_region_subset_safeCarrier ht, rfl⟩).trans (le_max_left _ _)

theorem integrableOn_sourceDensity_safeCarrier :
    IntegrableOn sourceDensity safeCarrier (volume : Measure Point) :=
  continuousOn_sourceDensity.integrableOn_compact isCompact_safeCarrier

theorem integrableOn_sourceDensity_closure_cell (c : Cell) :
    IntegrableOn sourceDensity (closure (cell c)) (volume : Measure Point) :=
  integrableOn_sourceDensity_safeCarrier.mono_set (closure_cell_subset_safeCarrier c)

theorem integrableOn_sourceDensity_closure_region :
    IntegrableOn sourceDensity (closure region) (volume : Measure Point) :=
  integrableOn_sourceDensity_safeCarrier.mono_set closure_region_subset_safeCarrier

theorem integrableOn_sourceDensity_region :
    IntegrableOn sourceDensity region (volume : Measure Point) :=
  integrableOn_sourceDensity_safeCarrier.mono_set region_subset_safeCarrier

theorem sourceDensity_pos_on_region {t : Point} (ht : t ∈ region) :
    0 < sourceDensity t := by
  obtain ⟨c, hc⟩ := mem_iUnion.mp ht
  exact (sourceRows_cellGuard c t hc).density_pos

end
end ImbalancedChen.P2OriginalSaving16FourteenPhysicalAtlas
