import ImbalancedChen.Certificates.P2PairedSemanticRestrictionError
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Push

/-!
SOURCE ONLY; uncompiled. The actual adopted rows are shrunk at every one
of their seven original walls. All omitted-volume and actual Buchstab-gain
limits below are proved from these literal sets, finite volume, and the
explicit semantic-density bound. No boundary-volume error is a premise.

This module proves a positive-buffer reserve for every positive requested
error. It does not assert a quantitative linear rate, historical-parent
containment of the shrunk region, or arithmetic wall-mass estimates.
-/

namespace ImbalancedChen.Certificates.PairedV2.FullMask.P2PairedBoundaryCollarReserve

noncomputable section

open MeasureTheory Set Filter
open scoped Topology
open P2AdoptedUnion P2SemanticGainSetIntegral P2PairedSemanticRestrictionError

/-- Literal inward collar: the original t,u endpoints, a<w, w<z, z<Z
all retain the same strictly positive buffer δ. -/
def shrunkSupport (r : Row) (δ : ℝ) : Set Point := {x |
  (tLower (indices r).1 : ℝ) + δ < x 0 ∧
  x 0 < (tUpper (indices r).1 : ℝ) - δ ∧
  (uLower (indices r).2 : ℝ) + δ < x 1 ∧
  x 1 < (uUpper (indices r).2 : ℝ) - δ ∧
  (a : ℝ) + δ < x 3 ∧ x 3 + δ < x 2 ∧ x 2 < (cutoff r : ℝ) - δ}

def shrunkRegion (δ : ℝ) : Set Point := ⋃ r : Row, shrunkSupport r δ

theorem shrunkSupport_zero (r : Row) : shrunkSupport r 0 = support r := by
  ext x
  simp [shrunkSupport, support, openFibreSet, openFibreSupport]

theorem shrunkRegion_zero : shrunkRegion 0 = region := by
  simp only [shrunkRegion, shrunkSupport_zero, region]

/-- The seven literal affine distances to the original row walls. The
ordering wall has margin z-w, so no independent rectangular replacement
of the triangular fibre is made. -/
def wallMargin (r : Row) (x : Point) : Fin 7 → ℝ :=
  ![x 0 - (tLower (indices r).1 : ℝ), (tUpper (indices r).1 : ℝ) - x 0,
    x 1 - (uLower (indices r).2 : ℝ), (uUpper (indices r).2 : ℝ) - x 1,
    x 3 - (a : ℝ), x 2 - x 3, (cutoff r : ℝ) - x 2]

def wallStrip (r : Row) (i : Fin 7) (δ : ℝ) : Set Point :=
  box ∩ {x | 0 < wallMargin r x i ∧ wallMargin r x i ≤ δ}

theorem continuous_wallMargin (r : Row) (i : Fin 7) :
    Continuous (fun x : Point => wallMargin r x i) := by
  fin_cases i <;> dsimp [wallMargin] <;> fun_prop

theorem wallStrip_measurable (r : Row) (i : Fin 7) (δ : ℝ) :
    MeasurableSet (wallStrip r i δ) := by
  exact measurableSet_Icc.inter
    ((isOpen_lt continuous_const (continuous_wallMargin r i)).measurableSet.inter
      (isClosed_le (continuous_wallMargin r i) continuous_const).measurableSet)

theorem support_wallMargin_pos (r : Row) {x : Point} (hx : x ∈ support r)
    (i : Fin 7) : 0 < wallMargin r x i := by
  rcases hx with ⟨htl, htr, hul, hur, haw, hwz, hzZ⟩
  fin_cases i <;> dsimp [wallMargin] <;> linarith

theorem mem_shrunkSupport_iff (r : Row) (δ : ℝ) (x : Point) :
    x ∈ shrunkSupport r δ ↔ ∀ i : Fin 7, δ < wallMargin r x i := by
  constructor
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩ i
    fin_cases i <;> dsimp [wallMargin] <;> linarith
  · intro h
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    have h3 := h 3
    have h4 := h 4
    have h5 := h 5
    have h6 := h 6
    change δ < x 0 - (tLower (indices r).1 : ℝ) at h0
    change δ < (tUpper (indices r).1 : ℝ) - x 0 at h1
    change δ < x 1 - (uLower (indices r).2 : ℝ) at h2
    change δ < (uUpper (indices r).2 : ℝ) - x 1 at h3
    change δ < x 3 - (a : ℝ) at h4
    change δ < x 2 - x 3 at h5
    change δ < (cutoff r : ℝ) - x 2 at h6
    exact ⟨by linarith, by linarith, by linarith, by linarith,
      by linarith, by linarith, by linarith⟩

/-- Every actually removed point lies in one of these seven genuine
affine strips in its original owner row. -/
theorem removed_subset_sevenWall_strips (δ : ℝ) :
    removed (shrunkRegion δ) ⊆ ⋃ r : Row, ⋃ i : Fin 7, wallStrip r i δ := by
  intro x hx
  obtain ⟨r, hr⟩ := mem_iUnion.mp hx.1
  have hn : ¬ ∀ i : Fin 7, δ < wallMargin r x i := by
    intro h
    exact hx.2 (mem_iUnion.mpr ⟨r, (mem_shrunkSupport_iff r δ x).mpr h⟩)
  push_neg at hn
  obtain ⟨i, hi⟩ := hn
  exact mem_iUnion.mpr ⟨r, mem_iUnion.mpr
    ⟨i, support_subset_box r hr, support_wallMargin_pos r hr i, hi⟩⟩

/-- A finite seven-wall geometric measure reserve, using the actual
product-volume strips. No value for any strip measure is assumed. -/
theorem omitted_volume_le_sevenWall_reserve (δ : ℝ) :
    volume (removed (shrunkRegion δ)) ≤
      ∑' r : Row, ∑' i : Fin 7, volume (wallStrip r i δ) := by
  calc
    _ ≤ volume (⋃ r : Row, ⋃ i : Fin 7, wallStrip r i δ) :=
      measure_mono (removed_subset_sevenWall_strips δ)
    _ ≤ ∑' r : Row, volume (⋃ i : Fin 7, wallStrip r i δ) := measure_iUnion_le _
    _ ≤ _ := ENNReal.tsum_le_tsum (fun r => measure_iUnion_le _)

theorem shrunkSupport_isOpen (r : Row) (δ : ℝ) : IsOpen (shrunkSupport r δ) := by
  exact (isOpen_lt continuous_const (continuous_apply 0)).inter
    ((isOpen_lt (continuous_apply 0) continuous_const).inter
    ((isOpen_lt continuous_const (continuous_apply 1)).inter
    ((isOpen_lt (continuous_apply 1) continuous_const).inter
    ((isOpen_lt continuous_const (continuous_apply 3)).inter
    ((isOpen_lt ((continuous_apply 3).add continuous_const) (continuous_apply 2)).inter
      (isOpen_lt (continuous_apply 2) continuous_const))))))

theorem shrunkRegion_measurable (δ : ℝ) : MeasurableSet (shrunkRegion δ) :=
  (isOpen_iUnion (fun r => shrunkSupport_isOpen r δ)).measurableSet

theorem shrunkSupport_subset_support (r : Row) {δ : ℝ} (hδ : 0 ≤ δ) :
    shrunkSupport r δ ⊆ support r := by
  intro x hx
  rcases hx with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  change (tLower (indices r).1 : ℝ) < x 0 ∧
    x 0 < (tUpper (indices r).1 : ℝ) ∧
    (uLower (indices r).2 : ℝ) < x 1 ∧
    x 1 < (uUpper (indices r).2 : ℝ) ∧
    (a : ℝ) < x 3 ∧ x 3 < x 2 ∧ x 2 < (cutoff r : ℝ)
  exact ⟨by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith, by linarith⟩

theorem shrunkRegion_subset_region {δ : ℝ} (hδ : 0 ≤ δ) : shrunkRegion δ ⊆ region := by
  intro x hx
  obtain ⟨r, hr⟩ := mem_iUnion.mp hx
  exact mem_iUnion.mpr ⟨r, shrunkSupport_subset_support r hδ hr⟩

/-- Larger inward buffer retains a smaller actual set. -/
theorem shrunkSupport_antitone (r : Row) {δ η : ℝ} (h : δ ≤ η) :
    shrunkSupport r η ⊆ shrunkSupport r δ := by
  intro x hx
  rcases hx with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  exact ⟨by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith, by linarith⟩

theorem shrunkRegion_antitone {δ η : ℝ} (h : δ ≤ η) : shrunkRegion η ⊆ shrunkRegion δ := by
  intro x hx
  obtain ⟨r, hr⟩ := mem_iUnion.mp hx
  exact mem_iUnion.mpr ⟨r, shrunkSupport_antitone r h hr⟩

def buffer (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem buffer_pos (n : ℕ) : 0 < buffer n := by unfold buffer; positivity

theorem buffer_antitone : Antitone buffer := by
  intro m n hmn
  exact one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (m : ℝ) + 1)
    (add_le_add_right (Nat.cast_le.mpr hmn) 1)

theorem buffer_tendsto : Tendsto buffer atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

def shrunkSequence (n : ℕ) : Set Point := shrunkRegion (buffer n)

theorem shrunkSequence_monotone : Monotone shrunkSequence := by
  intro m n hmn
  exact shrunkRegion_antitone (buffer_antitone hmn)

theorem eventually_mem_shrunkSupport (r : Row) {x : Point} (hx : x ∈ support r) :
    ∀ᶠ n : ℕ in atTop, x ∈ shrunkSupport r (buffer n) := by
  rcases hx with ⟨htl, htr, hul, hur, haw, hwz, hzZ⟩
  filter_upwards
    [buffer_tendsto.eventually_lt_const (sub_pos.mpr htl),
      buffer_tendsto.eventually_lt_const (sub_pos.mpr htr),
      buffer_tendsto.eventually_lt_const (sub_pos.mpr hul),
      buffer_tendsto.eventually_lt_const (sub_pos.mpr hur),
      buffer_tendsto.eventually_lt_const (sub_pos.mpr haw),
      buffer_tendsto.eventually_lt_const (sub_pos.mpr hwz),
      buffer_tendsto.eventually_lt_const (sub_pos.mpr hzZ)] with n h0 h1 h2 h3 h4 h5 h6
  exact ⟨by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith, by linarith⟩

/-- Every point of every original open row eventually survives all seven
walls; the genuine inward collars exhaust exactly the adopted region. -/
theorem iUnion_shrunkSequence : (⋃ n : ℕ, shrunkSequence n) = region := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    exact shrunkRegion_subset_region (buffer_pos n).le hn
  · intro x hx
    obtain ⟨r, hr⟩ := mem_iUnion.mp hx
    obtain ⟨n, hn⟩ := (eventually_mem_shrunkSupport r hr).exists
    exact mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨r, hn⟩⟩

theorem removedSequence_antitone : Antitone (fun n => removed (shrunkSequence n)) := by
  intro m n hmn x hx
  exact ⟨hx.1, fun hm => hx.2 (shrunkSequence_monotone hmn hm)⟩

theorem iInter_removedSequence : (⋂ n : ℕ, removed (shrunkSequence n)) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hx' : ∀ n : ℕ, x ∈ removed (shrunkSequence n) := mem_iInter.mp hx
  have hr : x ∈ region := (hx' 0).1
  have hu : x ∈ ⋃ n : ℕ, shrunkSequence n := by rwa [iUnion_shrunkSequence]
  obtain ⟨n, hn⟩ := mem_iUnion.mp hu
  exact (hx' n).2 hn

/-- Actual omitted product-volume tends to zero; no wall-volume premise. -/
theorem removedSequence_volume_tendsto :
    Tendsto (fun n => volume (removed (shrunkSequence n))) atTop (𝓝 0) := by
  have h := tendsto_measure_iInter_atTop (μ := volume)
    (fun n => (removed_measurable (shrunkRegion_measurable (buffer n))).nullMeasurableSet)
    removedSequence_antitone ⟨0, (removed_volume_lt_top (shrunkSequence 0)).ne⟩
  simpa only [Function.comp_def, iInter_removedSequence, measure_empty] using h

theorem removedSequence_volumeReal_tendsto :
    Tendsto (fun n => (volume (removed (shrunkSequence n))).toReal) atTop (𝓝 0) := by
  simpa only [ENNReal.toReal_zero] using
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp removedSequence_volume_tendsto

/-- The full right-hand positive-buffer limit, not merely convergence
along a chosen sequence. Monotonicity supplies the interpolation. -/
theorem removed_volumeReal_tendsto_zero_right :
    Tendsto (fun δ : ℝ => (volume (removed (shrunkRegion δ))).toReal)
      (𝓝[>] 0) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨n, hn⟩ := (removedSequence_volumeReal_tendsto.eventually_lt_const hε).exists
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (buffer_pos n)).filter_mono nhdsWithin_le_nhds] with δ hδ hδn
  have hsub : removed (shrunkRegion δ) ⊆ removed (shrunkSequence n) := by
    intro x hx
    exact ⟨hx.1, fun hx' => hx.2 (shrunkRegion_antitone hδn.le hx')⟩
  have hm : (volume (removed (shrunkRegion δ))).toReal ≤
      (volume (removed (shrunkSequence n))).toReal :=
    ENNReal.toReal_mono (removed_volume_lt_top (shrunkSequence n)).ne (measure_mono hsub)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg]
  exact hm.trans_lt hn

theorem removed_volume_tendsto_zero_right :
    Tendsto (fun δ : ℝ => volume (removed (shrunkRegion δ))) (𝓝[>] 0) (𝓝 0) :=
  (ENNReal.tendsto_toReal_zero_iff
    (fun δ => (removed_volume_lt_top (shrunkRegion δ)).ne)).mp
      removed_volumeReal_tendsto_zero_right

theorem collar_loss_tendsto_zero_right :
    Tendsto (fun δ : ℝ => lostGain (shrunkRegion δ)) (𝓝[>] 0) (𝓝 0) := by
  apply squeeze_zero (fun δ => lostGain_nonneg (shrunkRegion_measurable δ))
    (fun δ => lostGain_le_volume (shrunkRegion δ))
  simpa only [mul_zero] using
    removed_volumeReal_tendsto_zero_right.const_mul densityBound

theorem collarSequence_loss_tendsto :
    Tendsto (fun n : ℕ => lostGain (shrunkSequence n)) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => lostGain_nonneg (shrunkRegion_measurable (buffer n)))
    (fun n => lostGain_le_volume (shrunkSequence n))
  simpa only [mul_zero] using removedSequence_volumeReal_tendsto.const_mul densityBound

/-- A strictly positive literal buffer achieves every requested error
for the actual Buchstab gain, with the same frozen K/4 normalization. -/
theorem exists_positive_buffer_loss_le {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ lostGain (shrunkRegion δ) ≤ ε := by
  obtain ⟨n, hn⟩ := (collarSequence_loss_tendsto.eventually_lt_const hε).exists
  exact ⟨buffer n, buffer_pos n, hn.le⟩

theorem exists_positive_buffer_geometric_reserve {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ (volume (removed (shrunkRegion δ))).toReal < η := by
  obtain ⟨n, hn⟩ := (removedSequence_volumeReal_tendsto.eventually_lt_const hη).exists
  exact ⟨buffer n, buffer_pos n, hn⟩

/-- The actual collar retains the original lower endpoint up to an
arbitrarily small proved loss. This asserts no historical parent inclusion. -/
theorem exists_positive_buffer_retained_lower {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      (55858378943374979 / 100000000000000000000 : ℝ) - ε ≤
        retainedGain (shrunkRegion δ) := by
  obtain ⟨δ, hδ, hloss⟩ := exists_positive_buffer_loss_le hε
  refine ⟨δ, hδ, ?_⟩
  have he := full_sub_retained_eq_lost (shrunkRegion_measurable δ)
    (shrunkRegion_subset_region hδ.le)
  have hfull := unionSemanticIntegral_lower
  linarith

end

end ImbalancedChen.Certificates.PairedV2.FullMask.P2PairedBoundaryCollarReserve
