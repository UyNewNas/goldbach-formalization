import ImbalancedChen.P2U8UniformCoverConvergence
import Mathlib.Analysis.SpecificLimits.Basic

/-!
SOURCE ONLY / UNCOMPILED.

Global semantics of the explicit rational U8 upper quadrature. Shared
closed-cell walls are removed by the genuine product-measure Ico/Icc
almost-everywhere identity. Half-open cells are proved pairwise disjoint.
The error is then bounded by the local density oscillation on the fixed
rectangle plus density 1000 on the entire retained boundary staircase.
Both errors are O(1/M), with an explicit rational numerator.

No target endpoint or global error estimate is assumed. The final finite
certificate existence theorem has the honest premise that its proposed
rational endpoint lies strictly above the actual integral.
-/

namespace ImbalancedChen.P2U8QuadratureTendsto

noncomputable section

open MeasureTheory Set Filter Topology
open scoped BigOperators
open Classical
open P2NegativeDomainCover P2U8DirectedBoxEnclosure P2U8UniformRationalCover
open P2U8UniformCoverConvergence

def rectangleBox : Box := ⟨alpha, cubeWall, cubeWall, top⟩
def rectangle : Set Point := rectangleBox.region

theorem rectangleBox_valid : rectangleBox.Valid := by
  norm_num [rectangleBox, Box.Valid, alpha, cubeWall, top]

theorem mesh_subset_rectangle {M : ℕ} (hM : 0 < M) (ij : Fin M × Fin M) :
    (meshBox M ij).region ⊆ rectangle := by
  intro x hx
  obtain ⟨hxl, hxu, hyl, hyu⟩ := Box.mem_region.mp hx
  obtain ⟨ha, hb, hc, hd⟩ := meshBox_rectangle_guards hM ij
  have haR : (alpha : ℝ) ≤ ((meshBox M ij).xl : ℝ) := by exact_mod_cast ha
  have hbR : ((meshBox M ij).xu : ℝ) ≤ (cubeWall : ℝ) := by exact_mod_cast hb
  have hcR : (cubeWall : ℝ) ≤ ((meshBox M ij).yl : ℝ) := by exact_mod_cast hc
  have hdR : ((meshBox M ij).yu : ℝ) ≤ (top : ℝ) := by exact_mod_cast hd
  exact Box.mem_region.mpr ⟨haR.trans hxl, hxu.trans hbR, hcR.trans hyl, hyu.trans hdR⟩

def halfCell (M : ℕ) (ij : Fin M × Fin M) : Set Point :=
  logPrimeBox (meshBox M ij).lo (meshBox M ij).hi

theorem halfCell_subset (M : ℕ) (ij : Fin M × Fin M) :
    halfCell M ij ⊆ (meshBox M ij).region := by
  intro x hx
  have h := mem_logPrimeBox.mp hx
  exact ⟨fun i => (h i).1, fun i => (h i).2.le⟩

/-- The library theorem uses null real-coordinate singleton walls in the
actual product measure. This proves, rather than assumes, the wall step. -/
theorem halfCell_ae_closed (M : ℕ) (ij : Fin M × Fin M) :
    halfCell M ij =ᵐ[volume] (meshBox M ij).region := by
  unfold halfCell logPrimeBox Box.region
  rw [volume_pi]
  exact Measure.univ_pi_Ico_ae_eq_Icc

theorem uniform_sides_disjoint {a b : ℚ} (hab : a < b) {M : ℕ} (hM : 0 < M)
    {i j : ℕ} (hij : i ≠ j) :
    Disjoint (Ico ((node a b M i : ℚ) : ℝ) ((node a b M (i + 1) : ℚ) : ℝ))
      (Ico ((node a b M j : ℚ) : ℝ) ((node a b M (j + 1) : ℚ) : ℝ)) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hq := node_mono hab hM (Nat.succ_le_of_lt hlt)
    have hr : ((node a b M (i + 1) : ℚ) : ℝ) ≤ ((node a b M j : ℚ) : ℝ) := by exact_mod_cast hq
    linarith only [hx.2, hy.1, hr]
  · have hq := node_mono hab hM (Nat.succ_le_of_lt hgt)
    have hr : ((node a b M (j + 1) : ℚ) : ℝ) ≤ ((node a b M i : ℚ) : ℝ) := by exact_mod_cast hq
    linarith only [hy.2, hx.1, hr]

theorem halfCells_disjoint {M : ℕ} (hM : 0 < M) {ij kl : Fin M × Fin M}
    (hne : ij ≠ kl) : Disjoint (halfCell M ij) (halfCell M kl) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hix := mem_logPrimeBox.mp hx
  have hkx := mem_logPrimeBox.mp hy
  by_cases hfirst : ij.1 = kl.1
  · have hsecond : ij.2.val ≠ kl.2.val := by
      intro hv
      exact hne (Prod.ext hfirst (Fin.ext hv))
    have hd := uniform_sides_disjoint cubeWall_lt_top hM hsecond
    exact Set.disjoint_left.mp hd (hix 1) (hkx 1)
  · have hv : ij.1.val ≠ kl.1.val := fun hv => hfirst (Fin.ext hv)
    have hd := uniform_sides_disjoint alpha_lt_cubeWall hM hv
    exact Set.disjoint_left.mp hd (hix 0) (hkx 0)

theorem ae_cells_agree (M : ℕ) :
    ∀ᵐ x : Point ∂volume, ∀ ij : Fin M × Fin M,
      x ∈ (meshBox M ij).region ↔ x ∈ halfCell M ij := by
  apply ae_all_iff.mpr
  intro ij
  filter_upwards [halfCell_ae_closed M ij] with x hx
  exact (Iff.of_eq hx).symm

def closedUnion (M : ℕ) (s : Finset (Fin M × Fin M)) : Set Point :=
  ⋃ ij ∈ s, (meshBox M ij).region

def halfUnion (M : ℕ) (s : Finset (Fin M × Fin M)) : Set Point :=
  ⋃ ij ∈ s, halfCell M ij

theorem closedUnion_ae_halfUnion (M : ℕ) (s : Finset (Fin M × Fin M)) :
    closedUnion M s =ᵐ[volume] halfUnion M s := by
  filter_upwards [ae_cells_agree M] with x hx
  apply propext
  constructor
  · intro h
    obtain ⟨ij, h⟩ := mem_iUnion.mp h
    obtain ⟨hij, h⟩ := mem_iUnion.mp h
    exact mem_iUnion.mpr ⟨ij, mem_iUnion.mpr ⟨hij, (hx ij).mp h⟩⟩
  · intro h
    obtain ⟨ij, h⟩ := mem_iUnion.mp h
    obtain ⟨hij, h⟩ := mem_iUnion.mp h
    exact mem_iUnion.mpr ⟨ij, mem_iUnion.mpr ⟨hij, (hx ij).mpr h⟩⟩

/-- Genuine finite aggregation of the closed mesh integrals. The cells
need not be disjoint on their coordinate walls. -/
theorem closed_mesh_integral_aggregation {M : ℕ} (hM : 0 < M)
    (s : Finset (Fin M × Fin M)) (f : Point → ℝ)
    (hf : ∀ ij ∈ s, IntegrableOn f (meshBox M ij).region) :
    (∫ x in closedUnion M s, f x) = ∑ ij ∈ s, ∫ x in (meshBox M ij).region, f x := by
  calc
    _ = ∫ x in halfUnion M s, f x := setIntegral_congr_set (closedUnion_ae_halfUnion M s)
    _ = ∑ ij ∈ s, ∫ x in halfCell M ij, f x := by
      apply integral_biUnion_finset s
      · intro ij _
        exact measurableSet_logPrimeBox _ _
      · intro ij _ kl _ hne
        exact halfCells_disjoint hM hne
      · intro ij hij
        exact (hf ij hij).mono_set (halfCell_subset M ij)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro ij _
      exact setIntegral_congr_set (halfCell_ae_closed M ij)

theorem mesh_upper_le_1000 {M : ℕ} (hM : 0 < M) (ij : Fin M × Fin M) :
    (meshBox M ij).upper ≤ 1000 := by
  obtain ⟨ha, hb, hc, hd⟩ := meshBox_rectangle_guards hM ij
  have hapos : 0 < (meshBox M ij).xl := (by norm_num [alpha] : (0 : ℚ) < alpha).trans_le ha
  have hcpos : 0 < (meshBox M ij).yl := (by norm_num [cubeWall] : (0 : ℚ) < cubeWall).trans_le hc
  have hgap : (1 / 6 : ℚ) ≤ 1 - (meshBox M ij).xu - (meshBox M ij).yu := by
    have hfixed : 1 - cubeWall - top = (1 / 6 : ℚ) := by norm_num [cubeWall, top]
    linarith only [hb, hd, hfixed]
  have hprod : alpha * cubeWall ≤ (meshBox M ij).xl * (meshBox M ij).yl :=
    mul_le_mul ha hc (by norm_num [cubeWall]) hapos.le
  have hden : (1 / 1000 : ℚ) ≤
      (meshBox M ij).xl * (meshBox M ij).yl * (1 - (meshBox M ij).xu - (meshBox M ij).yu) := by
    calc
      (1 / 1000 : ℚ) ≤ alpha * cubeWall * (1 / 6) := by norm_num [alpha, cubeWall]
      _ ≤ (meshBox M ij).xl * (meshBox M ij).yl * (1 / 6) :=
        mul_le_mul_of_nonneg_right hprod (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_left hgap (mul_nonneg hapos.le hcpos.le)
  calc
    _ ≤ 1 / (1 / 1000 : ℚ) := one_div_le_one_div_of_le (by norm_num) hden
    _ = 1000 := by norm_num

theorem selected_extra_in_boundary {M : ℕ} (hM : 0 < M)
    {ij : Fin M × Fin M} (hij : ij ∈ selected M) {x : Point}
    (hx : x ∈ (meshBox M ij).region) (hxD : x ∉ eighthDomain) :
    x ∈ boundaryStaircase M := by
  have hrect := Box.mem_region.mp (mesh_subset_rectangle hM ij hx)
  have hgate : 1 ≤ x 0 + 2 * x 1 := by
    by_contra hnot
    have hg : x 0 + 2 * x 1 < 1 := lt_of_not_ge hnot
    apply hxD
    have ha : (417 / 5000 : ℝ) ≤ x 0 := by simpa [rectangleBox, alpha] using hrect.1
    have hxcap : x 0 ≤ (1 / 3 : ℝ) := by simpa [rectangleBox, cubeWall] using hrect.2.1
    have hc : (1 / 3 : ℝ) ≤ x 1 := by simpa [rectangleBox, cubeWall] using hrect.2.2.1
    refine ⟨mem_logPrimeBox.mpr ?_, ?_⟩
    · intro i
      fin_cases i
      · exact ⟨ha, by linarith only [hxcap]⟩
      · exact ⟨by linarith only [hc], by linarith only [ha, hg]⟩
    · change x 0 < 1 / 3 ∧ 1 / 3 ≤ x 1 ∧ x 0 + 2 * x 1 < 1
      exact ⟨by linarith only [hc, hg], hc, hg⟩
  obtain ⟨_, hxu, _, hyu⟩ := Box.mem_region.mp hx
  have hcrossR : (1 : ℝ) ≤ ((meshBox M ij).xu : ℝ) + 2 * (meshBox M ij).yu := by
    linarith only [hgate, hxu, hyu]
  have hcross : (1 : ℚ) ≤ (meshBox M ij).xu + 2 * (meshBox M ij).yu := by exact_mod_cast hcrossR
  exact mem_iUnion.mpr ⟨ij, mem_iUnion.mpr ⟨Finset.mem_filter.mpr ⟨hij, hcross⟩, hx⟩⟩

theorem boundary_subset_rectangle {M : ℕ} (hM : 0 < M) :
    boundaryStaircase M ⊆ rectangle := by
  intro x hx
  obtain ⟨ij, hx⟩ := mem_iUnion.mp hx
  obtain ⟨_, hx⟩ := mem_iUnion.mp hx
  exact mesh_subset_rectangle hM ij hx

theorem measurableSet_boundaryStaircase (M : ℕ) : MeasurableSet (boundaryStaircase M) := by
  exact Finset.measurableSet_biUnion (boundaryCells M) (fun _ _ => measurableSet_Icc)

def upperMajorant (M : ℕ) (x : Point) : ℝ := ∑ ij ∈ selected M, (meshBox M ij).majorant x

theorem integrable_upperMajorant (M : ℕ) : Integrable (upperMajorant M) :=
  integrable_finsetSum (selected M) (fun ij _ => Box.integrable_majorant (meshBox M ij))

theorem integral_upperMajorant {M : ℕ} (hM : 0 < M) :
    (∫ x, upperMajorant M x) = (uniformUpper M : ℝ) := by
  rw [upperMajorant, integral_finsetSum (selected M)
    (fun ij _ => Box.integrable_majorant (meshBox M ij))]
  calc
    _ = ∑ ij ∈ selected M, (((meshBox M ij).upper * (meshBox M ij).area : ℚ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro ij _
      exact Box.integral_majorant (meshBox_valid hM ij)
    _ = _ := by unfold uniformUpper; push_cast

def errorMajorant (M : ℕ) (x : Point) : ℝ :=
  rectangle.indicator (fun _ => (oscillationBudget M : ℝ)) x +
    (boundaryStaircase M).indicator (fun _ => (1000 : ℝ)) x

theorem oscillationBudget_nonneg {M : ℕ} (hM : 0 < M) : 0 ≤ (oscillationBudget M : ℝ) := by
  have hq : 0 ≤ oscillationBudget M := by
    unfold oscillationBudget
    exact div_nonneg (mul_nonneg (by norm_num) (by norm_num [top, alpha])) (Nat.cast_nonneg M)
  exact_mod_cast hq

theorem errorMajorant_nonneg {M : ℕ} (hM : 0 < M) (x : Point) : 0 ≤ errorMajorant M x := by
  apply add_nonneg
  · exact indicator_nonneg (fun _ _ => oscillationBudget_nonneg hM) x
  · exact indicator_nonneg (fun _ _ => (by norm_num : (0 : ℝ) ≤ 1000)) x

theorem integrable_errorMajorant {M : ℕ} (hM : 0 < M) : Integrable (errorMajorant M) := by
  have hrect : IntegrableOn (fun _ : Point => (oscillationBudget M : ℝ)) rectangle :=
    continuousOn_const.integrableOn_compact isCompact_Icc
  have hbound : IntegrableOn (fun _ : Point => (1000 : ℝ)) (boundaryStaircase M) :=
    (continuousOn_const.integrableOn_compact isCompact_Icc :
      IntegrableOn (fun _ : Point => (1000 : ℝ)) rectangle).mono_set (boundary_subset_rectangle hM)
  exact (hrect.integrable_indicator measurableSet_Icc).add
    (hbound.integrable_indicator (measurableSet_boundaryStaircase M))

/-- At almost every point, there is at most one closed mesh cell.
The cell's cap error is local inside U8, and is fully charged to the
boundary staircase outside U8. -/
theorem ae_quadrature_defect_le {M : ℕ} (hM : 0 < M) :
    ∀ᵐ x : Point ∂volume,
      upperMajorant M x - eighthDomain.indicator eighthDensity x ≤ errorMajorant M x := by
  filter_upwards [ae_cells_agree M] with x hagree
  by_cases hex : ∃ ij ∈ selected M, x ∈ (meshBox M ij).region
  · obtain ⟨ij, hij, hx⟩ := hex
    have hsum : upperMajorant M x = ((meshBox M ij).upper : ℝ) := by
      unfold upperMajorant
      calc
        _ = (meshBox M ij).majorant x := by
          apply Finset.sum_eq_single ij
          · intro kl _ hne
            have hnot : x ∉ (meshBox M kl).region := by
              intro hkl
              exact Set.disjoint_left.mp (halfCells_disjoint hM hne.symm)
                ((hagree ij).mp hx) ((hagree kl).mp hkl)
            exact indicator_of_notMem hnot _
          · intro hnot
            exact False.elim (hnot hij)
        _ = _ := indicator_of_mem hx _
    have hrect : x ∈ rectangle := mesh_subset_rectangle hM ij hx
    by_cases hxD : x ∈ eighthDomain
    · have hlocal := (mesh_actual_density_defect hM ij hx).2
      have hboundary : 0 ≤ (boundaryStaircase M).indicator (fun _ => (1000 : ℝ)) x :=
        indicator_nonneg (fun _ _ => by norm_num) x
      rw [hsum, indicator_of_mem hxD]
      unfold errorMajorant
      rw [indicator_of_mem hrect]
      linarith only [hlocal, hboundary]
    · have hxB := selected_extra_in_boundary hM hij hx hxD
      have hcap : ((meshBox M ij).upper : ℝ) ≤ 1000 := by exact_mod_cast mesh_upper_le_1000 hM ij
      rw [hsum, indicator_of_notMem hxD, sub_zero]
      unfold errorMajorant
      rw [indicator_of_mem hrect, indicator_of_mem hxB]
      exact hcap.trans (le_add_of_nonneg_left (oscillationBudget_nonneg hM))
  · have hnone : upperMajorant M x = 0 := by
      apply Finset.sum_eq_zero
      intro ij hij
      have hnot : x ∉ (meshBox M ij).region := fun hx => hex ⟨ij, hij, hx⟩
      exact indicator_of_notMem hnot _
    have hxD : x ∉ eighthDomain := by
      intro hxD
      exact hex (selected_covers_eighthDomain hM x hxD)
    rw [hnone, indicator_of_notMem hxD, sub_zero]
    exact errorMajorant_nonneg hM x

def errorNumerator : ℚ :=
  2000000 * (top - alpha) * rectangleBox.area +
    1000 * (cubeWall - alpha) * (1 - cubeWall - alpha)

/-- Explicit global O(1/M) error. Both shared-wall additivity and the
entire boundary staircase are paid by proofs above and in the predecessor. -/
theorem uniformUpper_error (M : ℕ) (hM : 0 < M) :
    0 ≤ (uniformUpper M : ℝ) - currentChenUpsilon8HarmonicIntegral ∧
      (uniformUpper M : ℝ) - currentChenUpsilon8HarmonicIntegral ≤
        (errorNumerator : ℝ) / (M : ℝ) := by
  have hD : Integrable (eighthDomain.indicator eighthDensity) :=
    integrableOn_eighthDensity.integrable_indicator measurableSet_eighthDomain
  have hmono := integral_mono_ae ((integrable_upperMajorant M).sub hD)
    (integrable_errorMajorant hM) (ae_quadrature_defect_le hM)
  rw [integral_sub (integrable_upperMajorant M) hD, integral_upperMajorant hM,
    integral_indicator measurableSet_eighthDomain] at hmono
  have hrect : Integrable (rectangle.indicator (fun _ => (oscillationBudget M : ℝ))) :=
    (continuousOn_const.integrableOn_compact isCompact_Icc :
      IntegrableOn (fun _ : Point => (oscillationBudget M : ℝ)) rectangle).integrable_indicator measurableSet_Icc
  have hbound : Integrable ((boundaryStaircase M).indicator (fun _ => (1000 : ℝ))) :=
    ((continuousOn_const.integrableOn_compact isCompact_Icc :
      IntegrableOn (fun _ : Point => (1000 : ℝ)) rectangle).mono_set
        (boundary_subset_rectangle hM)).integrable_indicator (measurableSet_boundaryStaircase M)
  have heval : (∫ x, errorMajorant M x) =
      (volume rectangle).toReal * (oscillationBudget M : ℝ) +
        (volume (boundaryStaircase M)).toReal * 1000 := by
    rw [errorMajorant, integral_add hrect hbound,
      integral_indicator measurableSet_Icc, integral_indicator (measurableSet_boundaryStaircase M),
      integral_const, integral_const]
    simp only [Measure.real, Measure.restrict_apply measurableSet_univ, univ_inter, smul_eq_mul]
  rw [heval] at hmono
  constructor
  · exact sub_nonneg.mpr (eighthIntegral_le_uniformUpper M hM)
  · calc
      _ ≤ (volume rectangle).toReal * (oscillationBudget M : ℝ) +
          (volume (boundaryStaircase M)).toReal * 1000 := hmono
      _ ≤ (rectangleBox.area : ℝ) * (oscillationBudget M : ℝ) +
          ((((cubeWall - alpha) * (1 - cubeWall - alpha) / (M : ℚ) : ℚ) : ℝ)) * 1000 := by
        rw [show (volume rectangle).toReal = (rectangleBox.area : ℝ) from Box.volume_real rectangleBox_valid]
        exact add_le_add_left (mul_le_mul_of_nonneg_right
          (boundaryStaircase_volume_explicit hM) (by norm_num : (0 : ℝ) ≤ 1000)) _
      _ = _ := by
        unfold oscillationBudget errorNumerator
        push_cast
        ring

theorem tendsto_uniformUpper :
    Tendsto (fun M : ℕ => (uniformUpper M : ℝ)) atTop (𝓝 currentChenUpsilon8HarmonicIntegral) := by
  have herror : Tendsto (fun M : ℕ => (errorNumerator : ℝ) / (M : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [herror.eventually (gt_mem_nhds hε), eventually_ge_atTop (1 : ℕ)] with M hsmall hM
  have hpos : 0 < M := by omega
  have hb := uniformUpper_error M hpos
  rw [Real.dist_eq, abs_of_nonneg hb.1]
  exact hb.2.trans_lt hsmall

/-- Any rational endpoint strictly above the actual integral eventually
has a finite exact-rational certificate. This does not assert that the
original selected endpoint has the required strict separation. -/
theorem exists_finite_endpointCheck (q : ℚ)
    (hq : currentChenUpsilon8HarmonicIntegral < (q : ℝ)) :
    ∃ M : ℕ, 0 < M ∧ endpointCheck M q = true := by
  have hevent : ∀ᶠ M : ℕ in atTop, (uniformUpper M : ℝ) < (q : ℝ) :=
    tendsto_uniformUpper.eventually (gt_mem_nhds hq)
  obtain ⟨M, hM, hlt⟩ := ((eventually_ge_atTop (1 : ℕ)).and hevent).exists
  refine ⟨M, by omega, ?_⟩
  change decide (uniformUpper M ≤ q) = true
  apply decide_eq_true_iff.mpr
  exact_mod_cast hlt.le

end

end ImbalancedChen.P2U8QuadratureTendsto
