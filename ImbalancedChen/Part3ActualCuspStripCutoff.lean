import ImbalancedChen.Part3Gamma0CuspMeasure
import ImbalancedChen.Part3GammaInfinityTranslationStrip
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# Actual hyperbolic single-cusp strip cutoffs

SOURCE_WRITTEN / UNCOMPILED / NOT_ROOT_ACCEPTED / CODE_ONLY.

A fixed native C-infinity bump, equal to one on [0,1] and zero on
[2,infinity), gives actual height cutoffs chi(y/Y). The canonical H
volume formula proves the exact high-strip mass w/Y. Actual chain rules,
compact derivative support, and the derived uniform derivative bound
give the L2 tail <= w/Y and vertical Dirichlet energy <= C_chi*w/Y.

Only the literal horizontal translation strip is involved. Neither
global Gamma0 invariance, a partition over all cusps, nor a global
constant-kernel or essential self-adjointness conclusion is asserted.
-/

namespace ImbalancedChen.Part3.ActualCuspStripCutoff20261025a

noncomputable section
open Set MeasureTheory Filter Topology Metric
open scoped UpperHalfPlane
open GammaInfinityTranslationStrip20261025a

/-- One fixed native smooth cutoff; no numerical approximation is used. -/
def cutoffBump : ContDiffBump (0 : ℝ) where
  rIn := 1
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def chi : ℝ → ℝ := cutoffBump

theorem chi_cinfty : ContDiff ℝ ∞ chi := cutoffBump.contDiff
theorem chi_compact : HasCompactSupport chi := cutoffBump.hasCompactSupport
theorem chi_nonneg (t : ℝ) : 0 ≤ chi t := cutoffBump.nonneg
theorem chi_le_one (t : ℝ) : chi t ≤ 1 := cutoffBump.le_one

theorem chi_eq_one {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : chi t = 1 := by
  apply cutoffBump.one_of_mem_closedBall
  simpa only [Metric.mem_closedBall,Real.dist_eq,sub_zero,abs_of_nonneg ht.1,
    cutoffBump] using ht.2

theorem chi_eq_zero {t : ℝ} (ht : 2 ≤ t) : chi t = 0 := by
  apply cutoffBump.zero_of_le_dist
  simpa only [Real.dist_eq,sub_zero,abs_of_nonneg (by linarith : 0 ≤ t),cutoffBump] using ht

theorem deriv_chi_zero_below {t : ℝ} (ht : 0 < t) (ht1 : t < 1) : deriv chi t = 0 := by
  have hball : t ∈ Metric.ball (0 : ℝ) cutoffBump.rIn := by
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos ht,cutoffBump] using ht1
  simpa only [deriv_const] using (cutoffBump.eventuallyEq_one_of_mem_ball hball).deriv_eq

theorem deriv_chi_zero_above {t : ℝ} (ht : 2 < t) : deriv chi t = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro h
  have hs := tsupport_deriv_subset h
  rw [show tsupport chi = Metric.closedBall (0 : ℝ) 2 from cutoffBump.tsupport_eq] at hs
  have : |t| ≤ 2 := by simpa only [Metric.mem_closedBall,Real.dist_eq,sub_zero] using hs
  exact (not_le_of_gt ht) ((le_abs_self t).trans this)

/-- A true global derivative bound is obtained from continuity on its
compact support, rather than supplied as an estimate on the tail. -/
theorem exists_derivative_bound : ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, |deriv chi t| ≤ B := by
  have hc : Continuous (deriv chi) := chi_cinfty.continuous_deriv (by simp)
  have hk : IsCompact (tsupport (deriv chi)) := chi_compact.deriv
  obtain ⟨b,hb⟩ := hk.bddAbove_image hc.norm.continuousOn
  refine ⟨max b 0,le_max_right _ _,?_⟩
  intro t
  by_cases ht : t ∈ tsupport (deriv chi)
  · exact (by simpa only [Real.norm_eq_abs] using hb ⟨t,ht,rfl⟩).trans (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport ht,abs_zero]
    exact le_max_right _ _

def derivativeBound : ℝ := Classical.choose exists_derivative_bound
theorem derivativeBound_nonneg : 0 ≤ derivativeBound :=
  (Classical.choose_spec exists_derivative_bound).1
theorem deriv_chi_bound (t : ℝ) : |deriv chi t| ≤ derivativeBound :=
  (Classical.choose_spec exists_derivative_bound).2 t

def cutoffEnergyConstant : ℝ := 4*derivativeBound^2
theorem cutoffEnergyConstant_nonneg : 0 ≤ cutoffEnergyConstant := by
  exact mul_nonneg (by norm_num) (sq_nonneg _)

def heightCutoff (Y : ℝ) (y : ℝ) : ℝ := chi (y/Y)

theorem heightCutoff_cinfty (Y : ℝ) : ContDiff ℝ ∞ (heightCutoff Y) :=
  chi_cinfty.comp (contDiff_id.div_const Y)

theorem deriv_heightCutoff (Y y : ℝ) :
    deriv (heightCutoff Y) y = deriv chi (y/Y)/Y := by
  have h := ((chi_cinfty.differentiable (by simp) (y/Y)).hasDerivAt).comp y
    ((hasDerivAt_id y).div_const Y)
  simpa only [heightCutoff,div_eq_mul_inv,one_mul] using h.deriv

theorem heightCutoff_eq_one {Y y : ℝ} (hY : 0 < Y) (hy : 0 ≤ y) (hyY : y ≤ Y) :
    heightCutoff Y y = 1 :=
  chi_eq_one ⟨div_nonneg hy hY.le,(div_le_one hY).mpr hyY⟩

theorem heightCutoff_eq_zero {Y y : ℝ} (hY : 0 < Y) (hy : 2*Y ≤ y) :
    heightCutoff Y y = 0 :=
  chi_eq_zero ((le_div_iff₀ hY).mpr hy)

def cutoffH (Y : ℝ) (z : UpperHalfPlane) : ℝ := heightCutoff Y z.im

def cutoffChart (Y : ℝ) (p : ℝ × ℝ) : ℝ := heightCutoff Y p.2

theorem cutoffChart_cinfty (Y : ℝ) : ContDiff ℝ ∞ (cutoffChart Y) :=
  (heightCutoff_cinfty Y).comp contDiff_snd

theorem cutoffChart_horizontal_deriv (Y x y : ℝ) :
    deriv (fun t => cutoffChart Y (t,y)) x = 0 := by
  exact deriv_const _ _

theorem cutoffChart_vertical_deriv (Y x y : ℝ) :
    deriv (fun t => cutoffChart Y (x,t)) y = deriv chi (y/Y)/Y :=
  deriv_heightCutoff Y y

/-- Exact actual parabolic translation invariance. -/
theorem cutoffH_translate (Y : ℝ) (k : ℤ) (z : UpperHalfPlane) :
    cutoffH Y (translate k z) = cutoffH Y z := by
  rw [translate_eq_vadd]
  simp only [cutoffH,UpperHalfPlane.vadd_im]

def widthStrip (w : ℝ) : Set UpperHalfPlane := {z | z.re ∈ Ico (0 : ℝ) w}
def highWidthStrip (w Y : ℝ) : Set UpperHalfPlane := {z | z.re ∈ Ico (0 : ℝ) w ∧ Y ≤ z.im}
def highRectangle (w Y : ℝ) : Set (ℝ × ℝ) := Ico (0 : ℝ) w ×ˢ Ici Y

theorem widthStrip_measurable (w : ℝ) : MeasurableSet (widthStrip w) :=
  UpperHalfPlane.continuous_re.measurable measurableSet_Ico

theorem highWidthStrip_measurable (w Y : ℝ) : MeasurableSet (highWidthStrip w Y) :=
  (widthStrip_measurable w).inter
    (UpperHalfPlane.continuous_im.measurable measurableSet_Ici)

theorem highWidthStrip_subset (w Y : ℝ) : highWidthStrip w Y ⊆ widthStrip w := fun _ h => h.1

private theorem highRectangle_integrable {w Y : ℝ} (hY : 0 < Y) :
    IntegrableOn (fun p : ℝ × ℝ => p.2 ^ (-2 : ℝ)) (highRectangle w Y) := by
  have hx : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ico (0 : ℝ) w) :=
    integrableOn_const (by simp)
  have hy : IntegrableOn (fun y : ℝ => y ^ (-2 : ℝ)) (Ici Y) :=
    integrableOn_Ici_iff_integrableOn_Ioi.mpr (integrableOn_Ioi_rpow_of_lt (by norm_num) hY)
  unfold highRectangle
  rw [Measure.volume_eq_prod,← Measure.prod_restrict]
  simpa only [one_mul] using hx.mul_prod hy

private theorem highRectangle_integral {w Y : ℝ} (hw : 0 ≤ w) (hY : 0 < Y) :
    (∫ p in highRectangle w Y, p.2 ^ (-2 : ℝ)) = w/Y := by
  have hy : (∫ y in Ici Y, y ^ (-2 : ℝ)) = 1/Y := by
    rw [integral_Ici_eq_integral_Ioi,integral_Ioi_rpow_of_lt (by norm_num) hY]
    norm_num [Real.rpow_neg_one]
  have hi := highRectangle_integrable (w := w) hY
  unfold highRectangle at hi ⊢
  rw [Measure.volume_eq_prod,← Measure.prod_restrict] at hi ⊢
  rw [integral_prod _ hi]
  simp only [hy,integral_const,Measure.restrict_apply_univ,Real.volume_Ico,
    sub_zero,ENNReal.toReal_ofReal hw,smul_eq_mul]
  ring

private theorem highStrip_complex_image {w Y : ℝ} (hY : 0 < Y) :
    UpperHalfPlane.coe '' highWidthStrip w Y =
      Complex.measurableEquivRealProd ⁻¹' highRectangle w Y := by
  ext z
  constructor
  · rintro ⟨u,hu,rfl⟩
    exact hu
  · intro hz
    have hp : 0 < z.im := hY.trans_le hz.2
    exact ⟨⟨z,hp⟩,hz,rfl⟩

private theorem nativeDensity_eq_rpow {z : ℂ} (hz : 0 < z.im) :
    (↑((1 / ‖z.im‖₊)^2 : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (z.im ^ (-2 : ℝ)) := by
  have hr : z.im ^ (-2 : ℝ) = (1/z.im)^2 := by
    rw [show (-2 : ℝ) = (-1 : ℝ)*2 by ring,Real.rpow_mul hz.le,
      Real.rpow_natCast,Real.rpow_neg_one]
    simp only [one_div]
  rw [hr,ENNReal.ofReal_eq_coe_nnreal (sq_nonneg _)]
  congr 1
  apply Subtype.ext
  simp [Real.nnnorm_of_nonneg hz.le,NNReal.coe_div,NNReal.coe_pow]

/-- Exact canonical hyperbolic volume, including the closed lower edge;
its singleton boundary has already been handled by the native integral API. -/
theorem highWidthStrip_volume {w Y : ℝ} (hw : 0 ≤ w) (hY : 0 < Y) :
    (volume : Measure UpperHalfPlane) (highWidthStrip w Y) = ENNReal.ofReal (w/Y) := by
  calc
    _ = ∫⁻ z : ℂ in UpperHalfPlane.coe '' highWidthStrip w Y,
        (↑((1 / ‖z.im‖₊)^2 : ℝ≥0) : ℝ≥0∞) := UpperHalfPlane.volume_eq_lintegral _
    _ = ∫⁻ z : ℂ in Complex.measurableEquivRealProd ⁻¹' highRectangle w Y,
        ENNReal.ofReal (z.im ^ (-2 : ℝ)) := by
      rw [highStrip_complex_image hY]
      apply setLIntegral_congr_fun ((measurableSet_Ico.prod measurableSet_Ici).preimage
        Complex.measurableEquivRealProd.measurable)
      intro z hz
      exact nativeDensity_eq_rpow (hY.trans_le hz.2)
    _ = ∫⁻ p in highRectangle w Y, ENNReal.ofReal (p.2 ^ (-2 : ℝ)) :=
      Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_preimage_emb
        Complex.measurableEquivRealProd.measurableEmbedding _ _
    _ = ENNReal.ofReal (∫ p in highRectangle w Y, p.2 ^ (-2 : ℝ)) := by
      symm
      apply ofReal_integral_eq_lintegral_ofReal (highRectangle_integrable hY)
      filter_upwards [ae_restrict_mem (measurableSet_Ico.prod measurableSet_Ici)] with p hp
      exact Real.rpow_nonneg (hY.le.trans hp.2) _
    _ = _ := by rw [highRectangle_integral hw hY]

/-- Elementary integration from a PRODUCED pointwise high-strip bound.
The applications below prove that bound from the actual fixed cutoff. -/
private theorem integral_le_highStrip_bound {w Y C : ℝ} (hw : 0 ≤ w) (hY : 0 < Y)
    (hC : 0 ≤ C) (f : UpperHalfPlane → ℝ)
    (hf : AEStronglyMeasurable f (volume.restrict (widthStrip w)))
    (hfn : ∀ z ∈ widthStrip w, 0 ≤ f z)
    (hfb : ∀ z ∈ widthStrip w, f z ≤ (highWidthStrip w Y).indicator (fun _ => C) z) :
    IntegrableOn f (widthStrip w) ∧ (∫ z in widthStrip w, f z) ≤ C*w/Y := by
  have hfin : (volume : Measure UpperHalfPlane) (highWidthStrip w Y) ≠ ∞ := by
    rw [highWidthStrip_volume hw hY]
    exact ENNReal.ofReal_ne_top
  have hi : Integrable ((highWidthStrip w Y).indicator (fun _ : UpperHalfPlane => C)) :=
    (integrable_indicator_iff (highWidthStrip_measurable w Y)).mpr (integrableOn_const hfin)
  have hfi : IntegrableOn f (widthStrip w) := hi.integrableOn.mono' hf (by
    filter_upwards [ae_restrict_mem (widthStrip_measurable w)] with z hz
    simpa only [Real.norm_eq_abs,abs_of_nonneg (hfn z hz)] using hfb z hz)
  refine ⟨hfi,?_⟩
  calc
    _ ≤ ∫ z in widthStrip w, (highWidthStrip w Y).indicator (fun _ => C) z := by
      apply integral_mono_ae hfi hi.integrableOn
      filter_upwards [ae_restrict_mem (widthStrip_measurable w)] with z hz
      exact hfb z hz
    _ = ∫ z in highWidthStrip w Y, C := by
      rw [setIntegral_indicator (highWidthStrip_measurable w Y),
        inter_eq_right.mpr (highWidthStrip_subset w Y)]
    _ = C*w/Y := by
      simp only [integral_const,Measure.restrict_apply_univ,Measure.real,
        highWidthStrip_volume hw hY,ENNReal.toReal_ofReal (div_nonneg hw hY.le),smul_eq_mul]
      ring

theorem cutoff_tail_pointwise {w Y : ℝ} (hY : 0 < Y) (z : UpperHalfPlane)
    (hz : z ∈ widthStrip w) :
    (1-cutoffH Y z)^2 ≤ (highWidthStrip w Y).indicator (fun _ => (1 : ℝ)) z := by
  by_cases hy : Y ≤ z.im
  · rw [indicator_of_mem (show z ∈ highWidthStrip w Y from ⟨hz,hy⟩)]
    have h0 := chi_nonneg (z.im/Y)
    have h1 := chi_le_one (z.im/Y)
    change (1-chi (z.im/Y))^2 ≤ 1
    nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1)]
  · rw [indicator_of_notMem (show z ∉ highWidthStrip w Y from fun h => hy h.2)]
    rw [cutoffH,heightCutoff_eq_one hY z.im_pos.le (lt_of_not_ge hy).le]
    norm_num

theorem cutoff_vertical_energy_pointwise {w Y : ℝ} (hY : 0 < Y)
    (z : UpperHalfPlane) (hz : z ∈ widthStrip w) :
    z.im^2*(deriv (heightCutoff Y) z.im)^2 ≤
      (highWidthStrip w Y).indicator (fun _ => cutoffEnergyConstant) z := by
  by_cases hy : Y ≤ z.im
  · rw [indicator_of_mem (show z ∈ highWidthStrip w Y from ⟨hz,hy⟩)]
    by_cases hy2 : z.im ≤ 2*Y
    · have hd : |deriv (heightCutoff Y) z.im| ≤ derivativeBound/Y := by
        rw [deriv_heightCutoff,abs_div,abs_of_pos hY]
        exact div_le_div_of_nonneg_right (deriv_chi_bound _) hY.le
      have hprod : |z.im*deriv (heightCutoff Y) z.im| ≤ 2*derivativeBound := by
        calc
          _ = z.im*|deriv (heightCutoff Y) z.im| := by rw [abs_mul,abs_of_pos z.im_pos]
          _ ≤ (2*Y)*(derivativeBound/Y) :=
            mul_le_mul hy2 hd (abs_nonneg _) (by positivity)
          _ = _ := by field_simp [hY.ne']; ring
      have hs := pow_le_pow_left₀ (abs_nonneg _) hprod 2
      simp only [sq_abs,mul_pow] at hs
      unfold cutoffEnergyConstant
      nlinarith
    · have hd : deriv (heightCutoff Y) z.im = 0 := by
        rw [deriv_heightCutoff,deriv_chi_zero_above ((lt_div_iff₀ hY).mpr (lt_of_not_ge hy2)),zero_div]
      rw [hd,mul_zero]
      exact cutoffEnergyConstant_nonneg
  · have hd : deriv (heightCutoff Y) z.im = 0 := by
      rw [deriv_heightCutoff,deriv_chi_zero_below (div_pos z.im_pos hY)
        ((div_lt_one hY).mpr (lt_of_not_ge hy)),zero_div]
    rw [hd,mul_zero,indicator_of_notMem (show z ∉ highWidthStrip w Y from fun h => hy h.2)]

/-- Canonical hyperbolic L2 tail of the actual single-cusp cutoff. -/
theorem cutoff_L2_tail {w Y : ℝ} (hw : 0 ≤ w) (hY : 0 < Y) :
    IntegrableOn (fun z : UpperHalfPlane => (1-cutoffH Y z)^2) (widthStrip w) ∧
      (∫ z in widthStrip w, (1-cutoffH Y z)^2) ≤ w/Y := by
  simpa only [one_mul] using integral_le_highStrip_bound hw hY (show (0 : ℝ) ≤ 1 by norm_num)
    (fun z => (1-cutoffH Y z)^2)
    (((continuous_const.sub ((heightCutoff_cinfty Y).continuous.comp
      UpperHalfPlane.continuous_im)).pow 2).aestronglyMeasurable.restrict)
    (fun z _ => sq_nonneg _) (cutoff_tail_pointwise hY)

/-- Canonical vertical Dirichlet energy is O(width/Y), with the one
fixed bump constant independent of height, strip width, and level. -/
theorem cutoff_Dirichlet_energy {w Y : ℝ} (hw : 0 ≤ w) (hY : 0 < Y) :
    IntegrableOn (fun z : UpperHalfPlane => z.im^2*(deriv (heightCutoff Y) z.im)^2)
      (widthStrip w) ∧
      (∫ z in widthStrip w, z.im^2*(deriv (heightCutoff Y) z.im)^2) ≤
        cutoffEnergyConstant*w/Y := by
  have hc : Continuous (deriv (heightCutoff Y)) :=
    (heightCutoff_cinfty Y).continuous_deriv (by simp)
  exact integral_le_highStrip_bound hw hY cutoffEnergyConstant_nonneg _
    (((UpperHalfPlane.continuous_im.pow 2).mul
      ((hc.comp UpperHalfPlane.continuous_im).pow 2)).aestronglyMeasurable.restrict)
    (fun z _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (cutoff_vertical_energy_pointwise hY)

theorem width_one_strip_eq : widthStrip 1 = strip := rfl

end
end ImbalancedChen.Part3.ActualCuspStripCutoff20261025a
