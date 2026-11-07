import ImbalancedChen.Part3ActualCuspStripCutoff
import ImbalancedChen.Part3ActualGamma0MaassDescent
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Actual single-cusp Maass cutoff graph budget

SOURCE_WRITTEN / UNCOMPILED / NOT_ROOT_ACCEPTED / CODE_ONLY.

The same native fixed cutoff chi is differentiated twice. Its second
derivative is continuous and compactly supported; its uniform bound B2
is derived here. The EXISTING native upperMaass of the actual height
cutoff is exactly -y^2*chi''(y/Y)/Y^2. It vanishes outside Y<=y<=2Y.
Canonical high-strip volume then gives its square integral at most
16*B2^2*w/Y. Together with the earlier actual L2 error estimate this
gives the affine constant-mode graph budget tending to zero.

On the full strip y>0 the constant and cutoff themselves need not be
L2 near zero. The conclusions concern their L2 DIFFERENCE and the L2
Maass output. On any high cusp with a positive fixed base height the
inputs are L2 as well. No global Gamma0 cutoff or operator-domain
membership is inferred from these single-cusp statements.
-/

namespace ImbalancedChen.Part3.ActualCuspStripCutoffGraph20261025a

noncomputable section
open Set MeasureTheory Filter Topology
open scoped UpperHalfPlane
open MaassWeakOperatorCore20261024zz
open ActualPoincareMaassLocalFinite20261025a
open ActualCuspStripCutoff20261025a

theorem deriv_chi_cinfty : ContDiff ℝ ∞ (deriv chi) := by
  have hc : ContDiff ℝ ((∞ : ℕ∞ω)+1) chi := by simpa using chi_cinfty
  exact hc.deriv'

theorem second_deriv_chi_continuous : Continuous (deriv (deriv chi)) :=
  deriv_chi_cinfty.continuous_deriv (by simp)

theorem second_deriv_chi_compact : HasCompactSupport (deriv (deriv chi)) :=
  chi_compact.deriv.deriv

theorem second_deriv_chi_zero_below {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    deriv (deriv chi) t = 0 := by
  have heq : deriv chi =ᶠ[𝓝 t] (fun _ => 0) := by
    filter_upwards [Ioo_mem_nhds ht ht1] with u hu
    exact deriv_chi_zero_below hu.1 hu.2
  simpa only [deriv_const] using heq.deriv_eq

theorem second_deriv_chi_zero_above {t : ℝ} (ht : 2 < t) :
    deriv (deriv chi) t = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro h
  have hs := tsupport_deriv_subset (tsupport_deriv_subset h)
  rw [show tsupport chi = Metric.closedBall (0 : ℝ) 2 from cutoffBump.tsupport_eq] at hs
  have hb : |t| ≤ 2 := by
    simpa only [Metric.mem_closedBall,Real.dist_eq,sub_zero] using hs
  exact (not_le_of_gt ht) ((le_abs_self t).trans hb)

/-- Uniform B2 is supplied by the actual compact second derivative,
not by any assumed Maass-tail or graph-norm estimate. -/
theorem exists_second_derivative_bound :
    ∃ B2 : ℝ, 0 ≤ B2 ∧ ∀ t : ℝ, |deriv (deriv chi) t| ≤ B2 := by
  obtain ⟨b,hb⟩ := second_deriv_chi_compact.bddAbove_image
    second_deriv_chi_continuous.norm.continuousOn
  refine ⟨max b 0,le_max_right _ _,?_⟩
  intro t
  by_cases ht : t ∈ tsupport (deriv (deriv chi))
  · exact (by simpa only [Real.norm_eq_abs] using hb ⟨t,ht,rfl⟩).trans (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport ht,abs_zero]
    exact le_max_right _ _

def secondDerivativeBound : ℝ := Classical.choose exists_second_derivative_bound
theorem secondDerivativeBound_nonneg : 0 ≤ secondDerivativeBound :=
  (Classical.choose_spec exists_second_derivative_bound).1
theorem second_deriv_chi_bound (t : ℝ) : |deriv (deriv chi) t| ≤ secondDerivativeBound :=
  (Classical.choose_spec exists_second_derivative_bound).2 t

def cutoffGraphConstant : ℝ := 16*secondDerivativeBound^2
theorem cutoffGraphConstant_nonneg : 0 ≤ cutoffGraphConstant := by
  exact mul_nonneg (by norm_num) (sq_nonneg _)

theorem second_deriv_heightCutoff (Y y : ℝ) :
    deriv (deriv (heightCutoff Y)) y = deriv (deriv chi) (y/Y)/Y^2 := by
  have hfirst : deriv (heightCutoff Y) = fun t => deriv chi (t/Y)/Y :=
    funext (deriv_heightCutoff Y)
  rw [hfirst]
  have h := (((deriv_chi_cinfty.differentiable (by simp) (y/Y)).hasDerivAt).comp y
    ((hasDerivAt_id y).div_const Y)).div_const Y
  simpa only [div_eq_mul_inv,one_mul,inv_pow,pow_two,mul_assoc] using h.deriv

private theorem heightCutoff_deriv_cinfty (Y : ℝ) :
    ContDiff ℝ ∞ (deriv (heightCutoff Y)) := by
  have hc : ContDiff ℝ ((∞ : ℕ∞ω)+1) (heightCutoff Y) := by
    simpa using heightCutoff_cinfty Y
  exact hc.deriv'

private theorem complex_height_deriv (Y y : ℝ) :
    deriv (fun t : ℝ => (heightCutoff Y t : ℂ)) y = (deriv (heightCutoff Y) y : ℂ) :=
  ((heightCutoff_cinfty Y).differentiable (by simp) y).hasDerivAt.ofReal_comp.deriv

private theorem complex_height_second_deriv (Y y : ℝ) :
    deriv (deriv (fun t : ℝ => (heightCutoff Y t : ℂ))) y =
      (deriv (deriv (heightCutoff Y)) y : ℂ) := by
  have hfirst : deriv (fun t : ℝ => (heightCutoff Y t : ℂ)) =
      fun t => (deriv (heightCutoff Y) t : ℂ) := funext (complex_height_deriv Y)
  rw [hfirst]
  exact ((heightCutoff_deriv_cinfty Y).differentiable (by simp) y).hasDerivAt.ofReal_comp.deriv

def complexCutoffH (Y : ℝ) (z : UpperHalfPlane) : ℂ := (cutoffH Y z : ℂ)
def complexCutoffChart (Y : ℝ) (p : ℝ × ℝ) : ℂ := (heightCutoff Y p.2 : ℂ)

/-- Locality is used on a genuine positive-height neighborhood, so the
native zero extension across y=0 is never differentiated at its edge. -/
theorem extend_complexCutoff_germ (Y : ℝ) {p : ℝ × ℝ} (hp : 0 < p.2) :
    extendUpper (complexCutoffH Y) =ᶠ[𝓝 p] complexCutoffChart Y := by
  filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds hp] with q hq
  simp only [extendUpper,dif_pos hq,complexCutoffH,cutoffH,complexCutoffChart]
  rfl

/-- The existing actual upperMaass, not a newly named formal profile. -/
theorem upperMaass_complexCutoff (Y : ℝ) (z : UpperHalfPlane) :
    upperMaass (complexCutoffH Y) z =
      -((z.im : ℂ)^2 * ((deriv (deriv chi) (z.im/Y)/Y^2 : ℝ) : ℂ)) := by
  change chartMaass (extendUpper (complexCutoffH Y)) (z.re,z.im) = _
  rw [chartMaass_eq_of_eventuallyEq (extend_complexCutoff_germ Y z.im_pos)]
  unfold chartMaass complexCutoffChart
  simp only [deriv_const',deriv_const,zero_add]
  rw [complex_height_second_deriv,second_deriv_heightCutoff]

theorem upperMaass_complexCutoff_continuous (Y : ℝ) :
    Continuous (upperMaass (complexCutoffH Y)) := by
  have heq : upperMaass (complexCutoffH Y) = fun z : UpperHalfPlane =>
      -((z.im : ℂ)^2*((deriv (deriv chi) (z.im/Y)/Y^2 : ℝ) : ℂ)) :=
    funext (upperMaass_complexCutoff Y)
  rw [heq]
  exact (((Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im).pow 2).mul
    (Complex.continuous_ofReal.comp ((second_deriv_chi_continuous.comp
      (UpperHalfPlane.continuous_im.div_const Y)).div_const (Y^2)))).neg

theorem upperMaass_complexCutoff_zero_of_outside {Y : ℝ} (hY : 0 < Y)
    (z : UpperHalfPlane) (hz : z.im < Y ∨ 2*Y < z.im) :
    upperMaass (complexCutoffH Y) z = 0 := by
  rw [upperMaass_complexCutoff]
  rcases hz with hlow | hhigh
  · rw [second_deriv_chi_zero_below (div_pos z.im_pos hY) ((div_lt_one hY).mpr hlow)]
    simp
  · rw [second_deriv_chi_zero_above ((lt_div_iff₀ hY).mpr hhigh)]
    simp

/-- Support lies in the actual height annulus Y<=y<=2Y. -/
theorem upperMaass_complexCutoff_support {Y : ℝ} (hY : 0 < Y) :
    Function.support (upperMaass (complexCutoffH Y)) ⊆
      {z : UpperHalfPlane | Y ≤ z.im ∧ z.im ≤ 2*Y} := by
  intro z hz
  by_contra h
  have hout : z.im < Y ∨ 2*Y < z.im := by
    simpa only [not_and_or,not_le] using h
  exact hz (upperMaass_complexCutoff_zero_of_outside hY z hout)

theorem upperMaass_complexCutoff_norm_sq_pointwise {w Y : ℝ} (hY : 0 < Y)
    (z : UpperHalfPlane) (hz : z ∈ widthStrip w) :
    ‖upperMaass (complexCutoffH Y) z‖^2 ≤
      (highWidthStrip w Y).indicator (fun _ => cutoffGraphConstant) z := by
  by_cases hy : Y ≤ z.im
  · rw [indicator_of_mem (show z ∈ highWidthStrip w Y from ⟨hz,hy⟩)]
    by_cases hy2 : z.im ≤ 2*Y
    · have hderiv : |deriv (deriv (heightCutoff Y)) z.im| ≤ secondDerivativeBound/Y^2 := by
        rw [second_deriv_heightCutoff,abs_div,abs_of_nonneg (sq_nonneg Y)]
        exact div_le_div_of_nonneg_right (second_deriv_chi_bound _) (sq_nonneg Y)
      have hprod : |z.im^2*deriv (deriv (heightCutoff Y)) z.im| ≤ 4*secondDerivativeBound := by
        calc
          _ = z.im^2*|deriv (deriv (heightCutoff Y)) z.im| := by
            rw [abs_mul,abs_of_nonneg (sq_nonneg _)]
          _ ≤ (2*Y)^2*(secondDerivativeBound/Y^2) :=
            mul_le_mul (pow_le_pow_left₀ z.im_pos.le hy2 2) hderiv (abs_nonneg _) (sq_nonneg _)
          _ = _ := by field_simp [hY.ne']; ring
      have hnorm : ‖upperMaass (complexCutoffH Y) z‖ =
          |z.im^2*deriv (deriv (heightCutoff Y)) z.im| := by
        rw [upperMaass_complexCutoff,← second_deriv_heightCutoff]
        simp only [norm_neg,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_pow,
          abs_mul]
      rw [hnorm]
      have hs := pow_le_pow_left₀ (abs_nonneg _) hprod 2
      unfold cutoffGraphConstant
      nlinarith
    · rw [upperMaass_complexCutoff_zero_of_outside hY z (Or.inr (lt_of_not_ge hy2)),norm_zero,zero_pow (by norm_num)]
      exact cutoffGraphConstant_nonneg
  · rw [upperMaass_complexCutoff_zero_of_outside hY z (Or.inl (lt_of_not_ge hy)),norm_zero,
      zero_pow (by norm_num),indicator_of_notMem (show z ∉ highWidthStrip w Y from fun h => hy h.2)]

/-- The actual native Maass output is square integrable on the strip,
and its bound is derived from canonical high-strip volume. -/
theorem cutoff_Maass_square_budget {w Y : ℝ} (hw : 0 ≤ w) (hY : 0 < Y) :
    IntegrableOn (fun z : UpperHalfPlane => ‖upperMaass (complexCutoffH Y) z‖^2) (widthStrip w) ∧
      (∫ z in widthStrip w, ‖upperMaass (complexCutoffH Y) z‖^2) ≤ cutoffGraphConstant*w/Y := by
  have hfin : (volume : Measure UpperHalfPlane) (highWidthStrip w Y) ≠ ∞ := by
    rw [highWidthStrip_volume hw hY]
    exact ENNReal.ofReal_ne_top
  have hi : Integrable ((highWidthStrip w Y).indicator (fun _ : UpperHalfPlane => cutoffGraphConstant)) :=
    (integrable_indicator_iff (highWidthStrip_measurable w Y)).mpr (integrableOn_const hfin)
  have hfi : IntegrableOn (fun z => ‖upperMaass (complexCutoffH Y) z‖^2) (widthStrip w) :=
    hi.integrableOn.mono' (((upperMaass_complexCutoff_continuous Y).norm.pow 2).aestronglyMeasurable.restrict)
      (by
        filter_upwards [ae_restrict_mem (widthStrip_measurable w)] with z hz
        simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)] using
          upperMaass_complexCutoff_norm_sq_pointwise hY z hz)
  refine ⟨hfi,?_⟩
  calc
    _ ≤ ∫ z in widthStrip w, (highWidthStrip w Y).indicator (fun _ => cutoffGraphConstant) z := by
      apply integral_mono_ae hfi hi.integrableOn
      filter_upwards [ae_restrict_mem (widthStrip_measurable w)] with z hz
      exact upperMaass_complexCutoff_norm_sq_pointwise hY z hz
    _ = ∫ z in highWidthStrip w Y, cutoffGraphConstant := by
      rw [setIntegral_indicator (highWidthStrip_measurable w Y),
        inter_eq_right.mpr (highWidthStrip_subset w Y)]
    _ = cutoffGraphConstant*w/Y := by
      simp only [integral_const,Measure.restrict_apply_univ,Measure.real,
        highWidthStrip_volume hw hY,ENNReal.toReal_ofReal (div_nonneg hw hY.le),smul_eq_mul]
      ring

private theorem norm_sq_error_eq (Y : ℝ) (z : UpperHalfPlane) :
    ‖(1 : ℂ)-complexCutoffH Y z‖^2 = (1-cutoffH Y z)^2 := by
  rw [show (1 : ℂ)-complexCutoffH Y z = ((1-cutoffH Y z : ℝ) : ℂ) by
    simp only [complexCutoffH,Complex.ofReal_sub,Complex.ofReal_one]]
  simp only [Complex.norm_real,Real.norm_eq_abs,sq_abs]

/-- Affine graph budget for the single-cusp constant mode. This is not
membership of the full-strip constant or cutoff itself in L2 near y=0. -/
theorem cutoff_affine_graph_budget {w Y : ℝ} (hw : 0 ≤ w) (hY : 0 < Y) :
    (∫ z in widthStrip w, ‖(1 : ℂ)-complexCutoffH Y z‖^2) +
      (∫ z in widthStrip w, ‖upperMaass (complexCutoffH Y) z‖^2) ≤
        (1+cutoffGraphConstant)*w/Y := by
  simp_rw [norm_sq_error_eq]
  have htail := (cutoff_L2_tail hw hY).2
  have hgraph := (cutoff_Maass_square_budget hw hY).2
  calc
    _ ≤ w/Y+cutoffGraphConstant*w/Y := add_le_add htail hgraph
    _ = _ := by ring

theorem cutoff_strip_L2_error_tendsto_zero {w : ℝ} (hw : 0 ≤ w) :
    Tendsto (fun Y : ℝ => ∫ z in widthStrip w, ‖(1 : ℂ)-complexCutoffH Y z‖^2)
      atTop (𝓝 0) := by
  have hmajor : Tendsto (fun Y : ℝ => w/Y) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using
      (tendsto_const_nhds.mul tendsto_inv_atTop_zero : Tendsto (fun Y : ℝ => w*Y⁻¹) atTop (𝓝 (w*0)))
  apply squeeze_zero' (Eventually.of_forall (fun Y => integral_nonneg (fun _ => sq_nonneg _))) ?_ hmajor
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with Y hY
  simpa only [norm_sq_error_eq] using (cutoff_L2_tail hw hY).2

theorem cutoff_strip_Maass_L2_tendsto_zero {w : ℝ} (hw : 0 ≤ w) :
    Tendsto (fun Y : ℝ => ∫ z in widthStrip w, ‖upperMaass (complexCutoffH Y) z‖^2)
      atTop (𝓝 0) := by
  have hmajor : Tendsto (fun Y : ℝ => cutoffGraphConstant*w/Y) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using
      (tendsto_const_nhds.mul tendsto_inv_atTop_zero :
        Tendsto (fun Y : ℝ => (cutoffGraphConstant*w)*Y⁻¹) atTop (𝓝 ((cutoffGraphConstant*w)*0)))
  apply squeeze_zero' (Eventually.of_forall (fun Y => integral_nonneg (fun _ => sq_nonneg _))) ?_ hmajor
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with Y hY
  exact (cutoff_Maass_square_budget hw hY).2

theorem cutoff_strip_affine_graph_tendsto_zero {w : ℝ} (hw : 0 ≤ w) :
    Tendsto (fun Y : ℝ =>
      (∫ z in widthStrip w, ‖(1 : ℂ)-complexCutoffH Y z‖^2) +
        (∫ z in widthStrip w, ‖upperMaass (complexCutoffH Y) z‖^2)) atTop (𝓝 0) := by
  simpa only [zero_add] using
    (cutoff_strip_L2_error_tendsto_zero hw).add (cutoff_strip_Maass_L2_tendsto_zero hw)

/-- With a positive fixed base height, the actual constant IS L2 for
the canonical cusp-strip measure. No full-strip constant L2 is asserted. -/
theorem highBase_constant_memLp_two {w a : ℝ} (hw : 0 ≤ w) (ha : 0 < a) :
    MemLp (fun _ : UpperHalfPlane => (1 : ℂ)) 2
      (volume.restrict (highWidthStrip w a)) := by
  letI : IsFiniteMeasure (volume.restrict (highWidthStrip w a)) :=
    isFiniteMeasure_restrict.mpr (by rw [highWidthStrip_volume hw ha]; exact ENNReal.ofReal_ne_top)
  exact MemLp.of_bound aestronglyMeasurable_const 1
    (Eventually.of_forall (fun _ => by simp only [norm_one,le_refl]))

theorem highBase_cutoff_memLp_two {w a : ℝ} (hw : 0 ≤ w) (ha : 0 < a) (Y : ℝ) :
    MemLp (complexCutoffH Y) 2 (volume.restrict (highWidthStrip w a)) := by
  letI : IsFiniteMeasure (volume.restrict (highWidthStrip w a)) :=
    isFiniteMeasure_restrict.mpr (by rw [highWidthStrip_volume hw ha]; exact ENNReal.ofReal_ne_top)
  have hc : Continuous (complexCutoffH Y) :=
    Complex.continuous_ofReal.comp ((heightCutoff_cinfty Y).continuous.comp UpperHalfPlane.continuous_im)
  apply MemLp.of_bound hc.aestronglyMeasurable.restrict 1
  apply Eventually.of_forall
  intro z
  simpa only [complexCutoffH,cutoffH,heightCutoff,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (chi_nonneg _)] using chi_le_one (z.im/Y)

theorem highBase_cutoff_Maass_memLp_two {w a Y : ℝ} (hw : 0 ≤ w) (hY : 0 < Y) :
    MemLp (upperMaass (complexCutoffH Y)) 2 (volume.restrict (highWidthStrip w a)) := by
  apply (memLp_two_iff_integrable_sq_norm
    (upperMaass_complexCutoff_continuous Y).aestronglyMeasurable.restrict).mpr
  exact (cutoff_Maass_square_budget hw hY).1.mono_set (highWidthStrip_subset w a)

/-- Restriction to any high cusp inherits the same produced graph bound;
positive base height additionally licenses the actual L2 input vectors. -/
theorem cutoff_highBase_affine_graph_budget {w a Y : ℝ} (hw : 0 ≤ w) (hY : 0 < Y) :
    (∫ z in highWidthStrip w a, ‖(1 : ℂ)-complexCutoffH Y z‖^2) +
      (∫ z in highWidthStrip w a, ‖upperMaass (complexCutoffH Y) z‖^2) ≤
        (1+cutoffGraphConstant)*w/Y := by
  have hiError : IntegrableOn (fun z : UpperHalfPlane => ‖(1 : ℂ)-complexCutoffH Y z‖^2)
      (widthStrip w) :=
    (cutoff_L2_tail hw hY).1.congr_fun (fun z _ => (norm_sq_error_eq Y z).symm)
      (widthStrip_measurable w)
  have hError := setIntegral_mono_set hiError
    (Eventually.of_forall (fun _ => sq_nonneg _))
    (Eventually.of_forall (highWidthStrip_subset w a))
  have hOutput := setIntegral_mono_set (cutoff_Maass_square_budget hw hY).1
    (Eventually.of_forall (fun _ => sq_nonneg _))
    (Eventually.of_forall (highWidthStrip_subset w a))
  exact (add_le_add hError hOutput).trans (cutoff_affine_graph_budget hw hY)

theorem cutoff_highBase_affine_graph_tendsto_zero {w a : ℝ} (hw : 0 ≤ w) :
    Tendsto (fun Y : ℝ =>
      (∫ z in highWidthStrip w a, ‖(1 : ℂ)-complexCutoffH Y z‖^2) +
        (∫ z in highWidthStrip w a, ‖upperMaass (complexCutoffH Y) z‖^2)) atTop (𝓝 0) := by
  have hmajor : Tendsto (fun Y : ℝ => ((1+cutoffGraphConstant)*w)/Y) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using
      (tendsto_const_nhds.mul tendsto_inv_atTop_zero :
        Tendsto (fun Y : ℝ => ((1+cutoffGraphConstant)*w)*Y⁻¹) atTop
          (𝓝 (((1+cutoffGraphConstant)*w)*0)))
  apply squeeze_zero' (Eventually.of_forall (fun Y => add_nonneg
    (integral_nonneg (fun _ => sq_nonneg _)) (integral_nonneg (fun _ => sq_nonneg _)))) ?_ hmajor
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with Y hY
  exact cutoff_highBase_affine_graph_budget hw hY

end
end ImbalancedChen.Part3.ActualCuspStripCutoffGraph20261025a
