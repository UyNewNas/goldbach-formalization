import ImbalancedChen.P4AOriginalFull87FiniteEighthCap
import ImbalancedChen.P4AOriginalFull87TrimOmission
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NO KERNEL CREDIT.

The manuscript's actual eighth saving density, with factor FOUR and no
Chen quarter or ordering factorial. The lower cutoff and residual bounds
are derived from the exact original87 Source, not supplied as a licence.
All estimates here concern real residual kernels. No arithmetic mean,
signed-frontier identity, archived numerical endpoint, or reserve is input.
-/
namespace ImbalancedChen.P4AOriginalFull87EighthKernelControl
noncomputable section
open scoped Classical BigOperators Topology ENNReal
open Set Filter MeasureTheory VariableEnvelope
open P4AOriginalFull87SourceDictionary
open P4AOriginalFull87StrictActionTrim
open P4AOriginalFull87FiniteEighthCap
open P4AOriginalFull87HistoryCore (width width_pos)
open P4AOriginalFull87TrimOmission (source_volume_lt_top)

/-- Exactly the adopted-source lower cutoff, not a chosen trim parameter. -/
def cutoff : ℝ := 53 / 13824

def total (t : Point) : ℝ := ∑ i, t i
def product (t : Point) : ℝ := ∏ i, t i

/-- The literal residual expression in eq:current-eighth-saving. -/
def residual (S J P M : ℝ) : ℝ := 4 * (M - P) / ((P - S) * (M - S) * J)
def kernel (c : Cell) (t : Point) : ℝ :=
  residual (total t) (product t) (comparison c t) (newCap c t)

def kernelBound : ℝ := 4 / cutoff ^ 9
def roundingConstant : ℝ := 8 / cutoff ^ 10

theorem cutoff_pos : 0 < cutoff := by norm_num [cutoff]
theorem kernelBound_pos : 0 < kernelBound :=
  div_pos (by norm_num) (pow_pos cutoff_pos 9)
theorem roundingConstant_pos : 0 < roundingConstant :=
  div_pos (by norm_num) (pow_pos cutoff_pos 10)

theorem source_coordinate_lower {c : Cell} {t : Point} (hs : Source c t) :
    ∀ i, cutoff < t i := by
  have ha : StrictAnti t := Fin.strictAnti_iff_succ_lt.mpr (source_basic hs).2.2.2
  intro i
  exact (source_basic hs).2.2.1.trans_le
    (ha.antitone (by have := i.isLt; omega))

theorem source_product_lower {c : Cell} {t : Point} (hs : Source c t) :
    cutoff ^ 8 ≤ product t ∧ 0 < product t := by
  have hcoord := source_coordinate_lower hs
  have hprod : (∏ _i : Fin 8, cutoff) ≤ ∏ i : Fin 8, t i :=
    Finset.prod_le_prod (fun _ _ => cutoff_pos.le) (fun i _ => (hcoord i).le)
  have hlo : cutoff ^ 8 ≤ product t := by simpa [product] using hprod
  exact ⟨hlo,(pow_pos cutoff_pos 8).trans_le hlo⟩

/-- Both residual denominators are bounded away from zero on the ENTIRE
original open source, independently of the extra compact trims. -/
theorem source_residual_range {c : Cell} {t : Point} (hs : Source c t) :
    cutoff < t 7 ∧ t 7 < comparison c t - total t ∧
      comparison c t < newCap c t ∧ newCap c t - total t < 3 * t 7 := by
  have hres := source_original_ideal_residual hs
  have hcomp := source_original_ideal_le_comparison hs
  have hgain := source_improvement_terminal hs
  exact ⟨source_coordinate_lower hs 7,by dsimp [total]; linarith,
    hgain.1,by dsimp [total]; linarith [hgain.2]⟩

theorem residual_eq_reciprocal (S J P M : ℝ)
    (hP : P - S ≠ 0) (hM : M - S ≠ 0) (hJ : J ≠ 0) :
    residual S J P M = 4 * (1 / (P - S) - 1 / (M - S)) / J := by
  unfold residual
  field_simp [hP,hM,hJ]
  <;> ring

theorem residual_nonneg (S J P M : ℝ)
    (hP : 0 < P - S) (hJ : 0 < J) (hPM : P ≤ M) :
    0 ≤ residual S J P M := by
  have hM : 0 < M - S := hP.trans_le (sub_le_sub_right hPM S)
  exact div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hPM))
    (mul_pos (mul_pos hP hM) hJ).le

/-- A comparison parent ABOVE the actual parent is conservative for this
residual expression. This is NOT monotonicity of arbitrary signed sums. -/
theorem residual_parent_mono (S J P R M : ℝ)
    (hP : 0 < P - S) (hJ : 0 < J) (hPR : P ≤ R) (hRM : R < M) :
    residual S J R M ≤ residual S J P M := by
  have hR : 0 < R - S := hP.trans_le (sub_le_sub_right hPR S)
  have hM : 0 < M - S := hR.trans (sub_lt_sub_right hRM S)
  rw [residual_eq_reciprocal S J R M hR.ne' hM.ne' hJ.ne',
    residual_eq_reciprocal S J P M hP.ne' hM.ne' hJ.ne']
  have hi : 1 / (R - S) ≤ 1 / (P - S) :=
    (div_le_div_iff₀ hR hP).mpr (by linarith)
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (sub_le_sub_right hi _) (by norm_num)) hJ.le

/-- Decreasing the new cap loses a precise amount independent of P. -/
theorem residual_endpoint_difference (S J P M L : ℝ)
    (hP : P - S ≠ 0) (hM : M - S ≠ 0) (hL : L - S ≠ 0) (hJ : J ≠ 0) :
    residual S J P M - residual S J P L =
      4 * (M - L) / ((L - S) * (M - S) * J) := by
  unfold residual
  field_simp [hP,hM,hL,hJ]
  <;> ring

theorem residual_bound (S J P M : ℝ)
    (hP : cutoff ≤ P - S) (hJ : cutoff ^ 8 ≤ J) (hPM : P < M) :
    0 ≤ residual S J P M ∧ residual S J P M ≤ kernelBound := by
  have ha := cutoff_pos
  have hp := cutoff_pos.trans_le hP
  have hj := (pow_pos cutoff_pos 8).trans_le hJ
  have hm : 0 < M - S := hp.trans (sub_lt_sub_right hPM S)
  refine ⟨residual_nonneg S J P M hp hj hPM.le,?_⟩
  rw [residual_eq_reciprocal S J P M hp.ne' hm.ne' hj.ne']
  have hi : 1 / (P - S) ≤ 1 / cutoff :=
    (div_le_div_iff₀ hp cutoff_pos).mpr (by linarith)
  have hdiff : 1 / (P - S) - 1 / (M - S) ≤ 1 / cutoff := by
    have hnonneg : 0 ≤ 1 / (M - S) := by positivity
    linarith
  calc
    _ ≤ (4 * (1 / cutoff)) / J :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hdiff (by norm_num)) hj.le
    _ ≤ (4 * (1 / cutoff)) / cutoff ^ 8 := by
      apply (div_le_div_iff₀ hj (pow_pos cutoff_pos 8)).mpr
      exact mul_le_mul_of_nonneg_left hJ (by positivity)
    _ = kernelBound := by
      unfold kernelBound
      field_simp [cutoff_pos.ne']
      <;> ring

theorem kernel_bounds {c : Cell} {t : Point} (hs : Source c t) :
    0 ≤ kernel c t ∧ kernel c t ≤ kernelBound := by
  have hr := source_residual_range hs
  exact residual_bound _ _ _ _ (hr.1.trans hr.2.1).le
    (source_product_lower hs).1 hr.2.2.1

theorem measurable_kernel (c : Cell) : Measurable (kernel c) := by
  have hR := (comparison_continuous c).measurable
  have hM := (newCap_continuous c).measurable
  have hS : Measurable total := by unfold total; fun_prop
  have hJ : Measurable product := by unfold product; fun_prop
  exact (measurable_const.mul (hM.sub hR)).div
    (((hR.sub hS).mul (hM.sub hS)).mul hJ)

/-- Actual kernel integrability is supplied here, NOT left as the generic
weight assumption used by the earlier omitted-volume statements. -/
theorem integrableOn_kernel (c : Cell) : IntegrableOn (kernel c) (sourceSet c) := by
  have hconst : IntegrableOn (fun _ : Point => kernelBound) (sourceSet c) :=
    integrableOn_const (source_volume_lt_top c).ne
  apply hconst.mono' (measurable_kernel c).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (sourceSet_measurable c)] with t ht
  rw [Real.norm_eq_abs,abs_of_nonneg (kernel_bounds ht).1]
  exact (kernel_bounds ht).2

/-- Exact endpoint loss with a uniform source cutoff. -/
theorem residual_rounding_loss (S J R M L h : ℝ)
    (hh : 0 ≤ h) (hR : cutoff ≤ R - S) (hRL : R < L)
    (hLM : L ≤ M) (hgap : M - L ≤ 2 * h) (hJ : cutoff ^ 8 ≤ J) :
    0 ≤ residual S J R M - residual S J R L ∧
      residual S J R M - residual S J R L ≤ roundingConstant * h := by
  have hp := cutoff_pos.trans_le hR
  have hl : 0 < L - S := hp.trans (sub_lt_sub_right hRL S)
  have hm : 0 < M - S := hl.trans_le (sub_le_sub_right hLM S)
  have hj := (pow_pos cutoff_pos 8).trans_le hJ
  have hal : cutoff ≤ L - S := hR.trans (sub_le_sub_right hRL.le S)
  have ham : cutoff ≤ M - S := hal.trans (sub_le_sub_right hLM S)
  have hab : cutoff * cutoff ≤ (L - S) * (M - S) :=
    mul_le_mul hal ham cutoff_pos.le hl.le
  have hden : cutoff ^ 10 ≤ (L - S) * (M - S) * J := by
    calc
      cutoff ^ 10 = (cutoff * cutoff) * cutoff ^ 8 := by ring
      _ ≤ ((L - S) * (M - S)) * J :=
        mul_le_mul hab hJ (pow_nonneg cutoff_pos.le 8) (mul_pos hl hm).le
  have hdenpos := mul_pos (mul_pos hl hm) hj
  rw [residual_endpoint_difference S J R M L hp.ne' hm.ne' hl.ne' hj.ne']
  refine ⟨div_nonneg (by nlinarith) hdenpos.le,?_⟩
  calc
    _ ≤ 8 * h / ((L - S) * (M - S) * J) :=
      div_le_div_of_nonneg_right (by linarith) hdenpos.le
    _ ≤ 8 * h / cutoff ^ 10 := by
      apply (div_le_div_iff₀ hdenpos (pow_pos cutoff_pos 10)).mpr
      exact mul_le_mul_of_nonneg_left hden (by positivity)
    _ = roundingConstant * h := by unfold roundingConstant; ring

end
end ImbalancedChen.P4AOriginalFull87EighthKernelControl
