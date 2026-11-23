import ImbalancedChen.P2U8UniformRationalCover
import Mathlib.MeasureTheory.Measure.Prod

/-!
SOURCE ONLY / UNCOMPILED.

Two concrete O(1/M) predecessors for convergence of the explicit U8 mesh:
* the actual whole-box cap oscillation is bounded uniformly by
  2000000*(1/2-417/5000)/M;
* the union of all retained boundary boxes has genuine Lebesgue volume
  at most (1/3-417/5000)*(1-1/3-417/5000)/M.

The second estimate is proved by exact product-measure slicing of a
diagonal strip. It is not a boundary-error hypothesis. The full global
upper-sum convergence statement still needs the finite mesh additivity
up to coordinate-wall null sets and aggregation of these estimates.
No adopted numerical endpoint is assumed or asserted.
-/

namespace ImbalancedChen.P2U8UniformCoverConvergence

noncomputable section

open MeasureTheory Set
open scoped BigOperators
open Classical
open P2NegativeDomainCover P2U8DirectedBoxEnclosure P2U8UniformRationalCover

theorem node_width (a b : ℚ) (M k : ℕ) :
    node a b M (k + 1) - node a b M k = step a b M := by
  simp only [node, Nat.cast_add, Nat.cast_one]
  ring

theorem meshBox_rectangle_guards {M : ℕ} (hM : 0 < M) (ij : Fin M × Fin M) :
    alpha ≤ (meshBox M ij).xl ∧ (meshBox M ij).xu ≤ cubeWall ∧
      cubeWall ≤ (meshBox M ij).yl ∧ (meshBox M ij).yu ≤ top := by
  exact ⟨start_le_node alpha_lt_cubeWall hM ij.1.val,
    node_le_end alpha_lt_cubeWall hM (Nat.succ_le_of_lt ij.1.isLt),
    start_le_node cubeWall_lt_top hM ij.2.val,
    node_le_end cubeWall_lt_top hM (Nat.succ_le_of_lt ij.2.isLt)⟩

/-- Algebraic reciprocal Lipschitz bound on the actual enclosing
rectangle. Its residual is at least 1/6, and its denominator exceeds
1/1000. The large constant is deliberately conservative. -/
theorem rational_cap_oscillation {a b c d : ℚ}
    (ha : alpha ≤ a) (hab : a ≤ b) (hb : b ≤ cubeWall)
    (hc : cubeWall ≤ c) (hcd : c ≤ d) (hd : d ≤ top) :
    1 / (a * c * (1 - b - d)) - 1 / (b * d * (1 - a - c)) ≤
      2000000 * ((b - a) + (d - c)) := by
  have hapos : 0 < a := (by norm_num [alpha] : (0 : ℚ) < alpha).trans_le ha
  have hcpos : 0 < c := (by norm_num [cubeWall] : (0 : ℚ) < cubeWall).trans_le hc
  have hbpos := hapos.trans_le hab
  have hdpos := hcpos.trans_le hcd
  have haone : a ≤ 1 := by
    have hfixed : cubeWall ≤ (1 : ℚ) := by norm_num [cubeWall]
    exact (hab.trans hb).trans hfixed
  have hdone : d ≤ 1 := by
    have hfixed : top ≤ (1 : ℚ) := by norm_num [top]
    exact hd.trans hfixed
  have hcone : c ≤ 1 := hcd.trans hdone
  have hgap : (1 / 6 : ℚ) ≤ 1 - b - d := by
    have hfixed : 1 - cubeWall - top = (1 / 6 : ℚ) := by norm_num [cubeWall, top]
    linarith only [hb, hd, hfixed]
  have hgap0 : 0 < 1 - b - d := lt_of_lt_of_le (by norm_num) hgap
  have hgap1 : 0 < 1 - a - c := by linarith only [hgap0, hab, hcd]
  have hprod : a * c ≤ b * d := mul_le_mul hab hcd hcpos.le hbpos.le
  have hac : alpha * cubeWall ≤ a * c :=
    mul_le_mul ha hc (by norm_num [cubeWall]) hapos.le
  have hlo : (1 / 1000 : ℚ) ≤ a * c * (1 - b - d) := by
    calc
      (1 / 1000 : ℚ) ≤ alpha * cubeWall * (1 / 6) := by norm_num [alpha, cubeWall]
      _ ≤ a * c * (1 / 6) := mul_le_mul_of_nonneg_right hac (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_left hgap (mul_nonneg hapos.le hcpos.le)
  have horder : a * c * (1 - b - d) ≤ b * d * (1 - a - c) := by
    calc
      _ ≤ b * d * (1 - b - d) := mul_le_mul_of_nonneg_right hprod hgap0.le
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith only [hab, hcd])
        (mul_nonneg hbpos.le hdpos.le)
  have hhi : (1 / 1000 : ℚ) ≤ b * d * (1 - a - c) := hlo.trans horder
  have hlowpos : 0 < a * c * (1 - b - d) := by linarith only [hlo]
  have hhighpos : 0 < b * d * (1 - a - c) := by linarith only [hhi]
  have hprodMin : (1 / 1000000 : ℚ) ≤
      (a * c * (1 - b - d)) * (b * d * (1 - a - c)) := by
    calc
      (1 / 1000000 : ℚ) = (1 / 1000) * (1 / 1000) := by norm_num
      _ ≤ _ := mul_le_mul hlo hhi (by norm_num) hhighpos.le
  have hwidth : 0 ≤ (b - a) + (d - c) := add_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hcd)
  have hprodDiff : b * d - a * c ≤ (b - a) + (d - c) := by
    have h1 := mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hdone)
    have h2 := mul_nonneg (sub_nonneg.mpr hcd) (sub_nonneg.mpr haone)
    nlinarith only [h1, h2]
  have hacone : a * c ≤ 1 := by
    calc
      a * c ≤ 1 * c := mul_le_mul_of_nonneg_right haone hcpos.le
      _ ≤ 1 := by simpa only [one_mul] using hcone
  have hpart1 : (b * d - a * c) * (1 - a - c) ≤ b * d - a * c := by
    have hle : 1 - a - c ≤ 1 := by linarith only [hapos, hcpos]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hle (sub_nonneg.mpr hprod)
  have hpart2 : a * c * ((b - a) + (d - c)) ≤ (b - a) + (d - c) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hacone hwidth
  have hdiff : b * d * (1 - a - c) - a * c * (1 - b - d) ≤
      2 * ((b - a) + (d - c)) := by
    have hid : b * d * (1 - a - c) - a * c * (1 - b - d) =
        (b * d - a * c) * (1 - a - c) + a * c * ((b - a) + (d - c)) := by ring
    linarith only [hid, hpart1, hpart2, hprodDiff]
  have hrecip : 1 / (a * c * (1 - b - d)) - 1 / (b * d * (1 - a - c)) =
      (b * d * (1 - a - c) - a * c * (1 - b - d)) /
        ((a * c * (1 - b - d)) * (b * d * (1 - a - c))) := by
    field_simp [hlowpos.ne', hhighpos.ne', hapos.ne', hbpos.ne', hcpos.ne',
      hdpos.ne', hgap0.ne', hgap1.ne'] <;> ring
  rw [hrecip]
  calc
    _ ≤ (b * d * (1 - a - c) - a * c * (1 - b - d)) / (1 / 1000000) :=
      div_le_div_of_nonneg_left (sub_nonneg.mpr horder) (by norm_num) hprodMin
    _ = 1000000 * (b * d * (1 - a - c) - a * c * (1 - b - d)) := by ring
    _ ≤ _ := by linarith only [hdiff]

def oscillationBudget (M : ℕ) : ℚ := 2000000 * (top - alpha) / (M : ℚ)

theorem mesh_cap_oscillation {M : ℕ} (hM : 0 < M) (ij : Fin M × Fin M) :
    (meshBox M ij).upper - (meshBox M ij).lower ≤ oscillationBudget M := by
  obtain ⟨ha, hb, hc, hd⟩ := meshBox_rectangle_guards hM ij
  have hv := meshBox_valid hM ij
  have hosc := rational_cap_oscillation ha hv.2.1 hb hc hv.2.2.2.1 hd
  have hxwidth : (meshBox M ij).xu - (meshBox M ij).xl = step alpha cubeWall M :=
    node_width _ _ _ _
  have hywidth : (meshBox M ij).yu - (meshBox M ij).yl = step cubeWall top M :=
    node_width _ _ _ _
  change (meshBox M ij).upper - (meshBox M ij).lower ≤ _ at hosc
  rw [hxwidth, hywidth] at hosc
  calc
    _ ≤ 2000000 * (step alpha cubeWall M + step cubeWall top M) := hosc
    _ = oscillationBudget M := by dsimp [step, oscillationBudget]; ring

/-- Actual local quadrature error for every point of the whole mesh box,
including points exterior to the strict U8 domain and all its walls. -/
theorem mesh_actual_density_defect {M : ℕ} (hM : 0 < M) (ij : Fin M × Fin M)
    {x : Point} (hx : x ∈ (meshBox M ij).region) :
    0 ≤ ((meshBox M ij).upper : ℝ) - eighthDensity x ∧
      ((meshBox M ij).upper : ℝ) - eighthDensity x ≤ (oscillationBudget M : ℝ) := by
  obtain ⟨hlo, hhi⟩ := Box.density_enclosure (meshBox_valid hM ij) hx
  have hosc : ((meshBox M ij).upper : ℝ) - (meshBox M ij).lower ≤ (oscillationBudget M : ℝ) := by
    exact_mod_cast mesh_cap_oscillation hM ij
  exact ⟨sub_nonneg.mpr hhi, by linarith only [hlo, hosc]⟩

/-- The corresponding actual full-box integral defect, rather than only
a comparison between stored corner values. -/
theorem mesh_actual_integral_defect {M : ℕ} (hM : 0 < M) (ij : Fin M × Fin M) :
    0 ≤ ((meshBox M ij).upper : ℝ) * (meshBox M ij).area -
      (∫ x in (meshBox M ij).region, eighthDensity x) ∧
    ((meshBox M ij).upper : ℝ) * (meshBox M ij).area -
      (∫ x in (meshBox M ij).region, eighthDensity x) ≤
        (oscillationBudget M : ℝ) * (meshBox M ij).area := by
  have hv := meshBox_valid hM ij
  have hareaQ : 0 ≤ (meshBox M ij).area :=
    mul_nonneg (sub_nonneg.mpr hv.2.1) (sub_nonneg.mpr hv.2.2.2.1)
  have harea : 0 ≤ ((meshBox M ij).area : ℝ) := by exact_mod_cast hareaQ
  obtain ⟨hlo, hhi⟩ := Box.integral_density_enclosure hv
  have hloR : ((meshBox M ij).lower : ℝ) * (meshBox M ij).area ≤
      (∫ x in (meshBox M ij).region, eighthDensity x) := by
    simpa only [Rat.cast_mul] using hlo
  have hhiR : (∫ x in (meshBox M ij).region, eighthDensity x) ≤
      ((meshBox M ij).upper : ℝ) * (meshBox M ij).area := by
    simpa only [Rat.cast_mul] using hhi
  have hosc : ((meshBox M ij).upper : ℝ) - (meshBox M ij).lower ≤ (oscillationBudget M : ℝ) := by
    exact_mod_cast mesh_cap_oscillation hM ij
  have hmul := mul_le_mul_of_nonneg_right hosc harea
  exact ⟨sub_nonneg.mpr hhiR, by nlinarith only [hloR, hmul]⟩

def gateWidth (M : ℕ) : ℚ := step alpha cubeWall M + 2 * step cubeWall top M

theorem gateWidth_pos {M : ℕ} (hM : 0 < M) : 0 < gateWidth M := by
  exact add_pos (step_pos alpha_lt_cubeWall hM)
    (mul_pos (by norm_num) (step_pos cubeWall_lt_top hM))

theorem gateWidth_eq (M : ℕ) : gateWidth M = (1 - cubeWall - alpha) / (M : ℚ) := by
  dsimp [gateWidth, step, alpha, cubeWall, top]
  ring

/-- Retained boxes crossing or touching the affine U8 boundary. -/
def boundaryCells (M : ℕ) : Finset (Fin M × Fin M) :=
  (selected M).filter fun ij => 1 ≤ (meshBox M ij).xu + 2 * (meshBox M ij).yu

def boundaryStaircase (M : ℕ) : Set Point :=
  ⋃ ij ∈ boundaryCells M, (meshBox M ij).region

def pairStrip (δ : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Icc (alpha : ℝ) (cubeWall : ℝ) ∧
    p.2 ∈ Icc ((1 - δ - p.1) / 2) ((1 + δ - p.1) / 2)}

def coordinateEquiv := MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)
def diagonalStrip (δ : ℝ) : Set Point := coordinateEquiv ⁻¹' pairStrip δ

theorem measurableSet_pairStrip (δ : ℝ) : MeasurableSet (pairStrip δ) := by
  have hlo : Continuous (fun p : ℝ × ℝ => (1 - δ - p.1) / 2) := by fun_prop
  have hhi : Continuous (fun p : ℝ × ℝ => (1 + δ - p.1) / 2) := by fun_prop
  exact ((measurableSet_le measurable_const continuous_fst.measurable).inter
    (measurableSet_le continuous_fst.measurable measurable_const)).inter
      ((measurableSet_le hlo.measurable continuous_snd.measurable).inter
        (measurableSet_le continuous_snd.measurable hhi.measurable))

/-- Exact product-measure calculation; the moving vertical slice has
width δ for every first coordinate in the original x interval. -/
theorem volume_pairStrip (δ : ℝ) :
    volume (pairStrip δ) = ENNReal.ofReal δ * ENNReal.ofReal ((cubeWall : ℝ) - alpha) := by
  have hfibre (x : ℝ) : volume (Prod.mk x ⁻¹' pairStrip δ) =
      (Icc (alpha : ℝ) (cubeWall : ℝ)).indicator (fun _ => ENNReal.ofReal δ) x := by
    by_cases hx : x ∈ Icc (alpha : ℝ) (cubeWall : ℝ)
    · rw [indicator_of_mem hx]
      have hs : Prod.mk x ⁻¹' pairStrip δ = Icc ((1 - δ - x) / 2) ((1 + δ - x) / 2) := by
        ext y
        simp only [pairStrip, mem_preimage, mem_setOf_eq, hx, true_and]
      rw [hs, Real.volume_Icc]
      congr 1
      ring
    · have hs : Prod.mk x ⁻¹' pairStrip δ = ∅ := by
        ext y
        simp only [pairStrip, mem_preimage, mem_setOf_eq, hx, false_and, mem_empty_iff_false]
      rw [hs, measure_empty, indicator_of_notMem hx]
  rw [volume_prod, Measure.prod_apply (measurableSet_pairStrip δ)]
  simp_rw [hfibre]
  rw [lintegral_indicator measurableSet_Icc, lintegral_const]
  simp only [Measure.restrict_apply measurableSet_univ, univ_inter, Real.volume_Icc]

theorem volume_diagonalStrip (δ : ℝ) :
    volume (diagonalStrip δ) = ENNReal.ofReal δ * ENNReal.ofReal ((cubeWall : ℝ) - alpha) := by
  have hE : MeasurePreserving coordinateEquiv := volume_preserving_piFinTwo _
  calc
    volume (diagonalStrip δ) = (Measure.map coordinateEquiv volume) (pairStrip δ) :=
      (Measure.map_apply hE.measurable (measurableSet_pairStrip δ)).symm
    _ = volume (pairStrip δ) := by rw [hE.map_eq]
    _ = _ := volume_pairStrip δ

/-- The entire closed boundary staircase is contained in a proved strip;
both sides of the sloping boundary are charged. -/
theorem boundaryStaircase_subset_strip {M : ℕ} (hM : 0 < M) :
    boundaryStaircase M ⊆ diagonalStrip (gateWidth M : ℝ) := by
  intro x hx
  obtain ⟨ij, hx⟩ := mem_iUnion.mp hx
  obtain ⟨hij, hbox⟩ := mem_iUnion.mp hx
  obtain ⟨hselected, hcross⟩ := Finset.mem_filter.mp hij
  have hlow := (Finset.mem_filter.mp hselected).2
  obtain ⟨hxl, hxu, hyl, hyu⟩ := Box.mem_region.mp hbox
  obtain ⟨ha, hb, hc, hd⟩ := meshBox_rectangle_guards hM ij
  have hspanQ : (meshBox M ij).xu + 2 * (meshBox M ij).yu -
      ((meshBox M ij).xl + 2 * (meshBox M ij).yl) = gateWidth M := by
    dsimp [meshBox, gateWidth, node]
    simp only [Nat.cast_add, Nat.cast_one]
    ring
  have hspan : ((meshBox M ij).xu : ℝ) + 2 * (meshBox M ij).yu -
      (((meshBox M ij).xl : ℝ) + 2 * (meshBox M ij).yl) = (gateWidth M : ℝ) := by
    exact_mod_cast hspanQ
  have hloR : ((meshBox M ij).xl : ℝ) + 2 * (meshBox M ij).yl ≤ 1 := by exact_mod_cast hlow
  have hhiR : (1 : ℝ) ≤ ((meshBox M ij).xu : ℝ) + 2 * (meshBox M ij).yu := by exact_mod_cast hcross
  have haR : (alpha : ℝ) ≤ ((meshBox M ij).xl : ℝ) := by exact_mod_cast ha
  have hbR : ((meshBox M ij).xu : ℝ) ≤ (cubeWall : ℝ) := by exact_mod_cast hb
  change ((alpha : ℝ) ≤ x 0 ∧ x 0 ≤ (cubeWall : ℝ)) ∧
    ((1 - (gateWidth M : ℝ) - x 0) / 2 ≤ x 1 ∧
    x 1 ≤ (1 + (gateWidth M : ℝ) - x 0) / 2)
  exact ⟨⟨haR.trans hxl, hxu.trans hbR⟩,
    ⟨by linarith only [hxl, hyl, hhiR, hspan],
    by linarith only [hxu, hyu, hloR, hspan]⟩⟩

/-- A genuine full-boundary volume bound, with an explicit O(1/M) width.
No boundary-area estimate occurs among the assumptions. -/
theorem boundaryStaircase_volume_real {M : ℕ} (hM : 0 < M) :
    (volume (boundaryStaircase M)).toReal ≤
      (gateWidth M : ℝ) * ((cubeWall : ℝ) - alpha) := by
  have hmeasure : volume (boundaryStaircase M) ≤ volume (diagonalStrip (gateWidth M : ℝ)) :=
    measure_mono (boundaryStaircase_subset_strip hM)
  rw [volume_diagonalStrip] at hmeasure
  have hfinite : ENNReal.ofReal (gateWidth M : ℝ) *
      ENNReal.ofReal ((cubeWall : ℝ) - alpha) ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) (by simp)
  have hreal := ENNReal.toReal_mono hfinite hmeasure
  have hδ : 0 ≤ (gateWidth M : ℝ) := by exact_mod_cast (gateWidth_pos hM).le
  have hxwidth : 0 ≤ (cubeWall : ℝ) - alpha := by exact_mod_cast sub_nonneg.mpr alpha_lt_cubeWall.le
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hδ,
    ENNReal.toReal_ofReal hxwidth] using hreal

theorem boundaryStaircase_volume_explicit {M : ℕ} (hM : 0 < M) :
    (volume (boundaryStaircase M)).toReal ≤
      (((cubeWall - alpha) * (1 - cubeWall - alpha) / (M : ℚ) : ℚ) : ℝ) := by
  calc
    _ ≤ (gateWidth M : ℝ) * ((cubeWall : ℝ) - alpha) := boundaryStaircase_volume_real hM
    _ = _ := by rw [gateWidth_eq]; push_cast; ring

end

end ImbalancedChen.P2U8UniformCoverConvergence
