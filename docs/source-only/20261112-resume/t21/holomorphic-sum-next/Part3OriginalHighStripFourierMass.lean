import ImbalancedChen.Part3OriginalPeterssonHighStrip

/-! The actual q-expansion coefficient on a full normalized horizontal period, integrated
against the vertical Petersson density in the physical high strip. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalHighStripFourierMass20261112
open Set MeasureTheory Matrix UpperHalfPlane Complex
open scoped MatrixGroups UpperHalfPlane ModularForm BigOperators ENNReal
open CanonicalPlanarL2UnitarySourceOnly (chartMap chartMap_measurableEmbedding)
open MaassWeightedCoordinateL220261024zz (verticalWeightedMeasure verticalWeight verticalWeight_measurable)
open ActualHighStripCircleMeasure20261026b (highStrip_chart_map_measure)
open ActualCuspStripCutoff20261025a (highWidthStrip)
open OriginalPeterssonHighStrip20261112
open OriginalHolomorphicCuspFrames20261110 OriginalHolomorphicPeterssonSpace20261112
open OriginalPeterssonPretrace20261112 (raw)
open OriginalHeckeStripPairing20261112 (q q_norm)
open scoped OriginalHolomorphicPeterssonSpace20261112

private abbrev unitMeasure : Measure ℝ := volume.restrict (Ico 0 1)
private instance : IsProbabilityMeasure unitMeasure :=
  ⟨by simp [unitMeasure,Real.volume_Ico]⟩

private theorem mean_square {F : ℝ→ℂ} (hf : Continuous F) :
    ‖∫ x,F x ∂unitMeasure‖^2≤∫ x,‖F x‖^2 ∂unitMeasure := by
  let b := ∫ x,‖F x‖ ∂unitMeasure
  have hi : Integrable (fun x => ‖F x‖) unitMeasure :=
    (hf.norm.integrableOn_compact isCompact_Icc).mono_set Ico_subset_Icc_self
  have hs : Integrable (fun x => ‖F x‖^2) unitMeasure :=
    ((hf.norm.pow 2).integrableOn_compact isCompact_Icc).mono_set Ico_subset_Icc_self
  have pos := integral_nonneg (μ:=unitMeasure) (fun x : ℝ => sq_nonneg (‖F x‖-b))
  simp_rw [show ∀ x : ℝ,(‖F x‖-b)^2=(‖F x‖^2-(2*b)*‖F x‖)+b^2 by intro x;ring] at pos
  rw [integral_add (hs.sub (hi.const_mul _)) (integrable_const _),
    integral_sub hs (hi.const_mul _),integral_const_mul,integral_const] at pos
  simp only [probReal_univ,one_smul] at pos
  have h1 : ‖∫ x,F x ∂unitMeasure‖≤b := norm_integral_le_integral_norm _
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans (by dsimp [b] at *;nlinarith)

private def point (x y : ℝ) (hy : 0<y) : ℍ := ⟨(x:ℂ)+y*I,by simpa using hy⟩

private theorem point_cont (y : ℝ) (hy : 0<y) : Continuous (fun x : ℝ => point x y hy) :=
  Continuous.subtype_mk (by dsimp [point];fun_prop) _

/-- Horizontal orthogonal coefficient estimate on the unscaled Haar interval of length one. -/
theorem horizontal_square (N r : ℕ) [NeZero N] (f : Forms N r) (g : SL(2,ℤ))
    (m : ℕ) {y : ℝ} (hy : 0<y) :
    Real.exp (-(4*Real.pi*m*y))*‖raw N (NeZero.pos N) r g m f‖^2 ≤
      ∫ x,‖frameForm N (NeZero.pos N) r f g (point x y hy)‖^2 ∂unitMeasure := by
  let F := frameForm N (NeZero.pos N) r f g
  let a := Real.exp (-(2*Real.pi*m*y))
  let U := fun x => (1/q (point x y hy)^m)*F (point x y hy)
  have a0 : 0<a := Real.exp_pos _
  have iq : (∫ x,U x ∂unitMeasure)=raw N (NeZero.pos N) r g m f := by
    rw [show (∫ x,U x ∂unitMeasure)=∫ x in (0:ℝ)..1,U x by
      rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
      exact integral_Ico_eq_integral_Ioc]
    simpa [U,point,F,raw,q] using
      (ModularFormClass.qExpansion_coeff_eq_intervalIntegral F (by norm_num : (0:ℝ)<1)
        (normalized_frame_unit_strictPeriod N (NeZero.pos N) g) m hy).symm
  have hc : Continuous U := by
    refine (continuous_const.div (((Function.Periodic.continuous_qParam 1).comp
      (continuous_coe.comp (point_cont y hy))).pow _) (fun _ => pow_ne_zero _ (Function.Periodic.qParam_ne_zero 1 _))).mul
        ((ModularFormClass.holo F).continuous.comp (point_cont y hy))
  have hn (x : ℝ) : ‖(a:ℂ)*U x‖=‖F (point x y hy)‖ := by
    have hq : ‖q (point x y hy)^m‖=a := by simpa [a,point] using q_norm (point x y hy) m
    simp only [U,norm_mul,norm_div,norm_one,Complex.norm_real,Real.norm_of_nonneg a0.le,hq]
    field_simp [a0.ne']
  have H := mean_square (continuous_const.mul hc : Continuous (fun x => (a:ℂ)*U x))
  simp_rw [hn] at H
  rw [integral_const_mul,iq,norm_mul,Complex.norm_real,Real.norm_of_nonneg a0.le,mul_pow] at H
  have he : a^2=Real.exp (-(4*Real.pi*m*y)) := by
    rw [a,sq,←Real.exp_add];congr 1;ring
  rwa [he] at H

private def plane {N r : ℕ} [NeZero N] (f : Forms N r) (g : SL(2,ℤ)) : ℝ×ℝ→ℝ≥0∞ :=
  Function.extend chartMap (frameEnergy f g) 0

private theorem plane_meas {N r : ℕ} [NeZero N] (f : Forms N r) (g : SL(2,ℤ)) :
    Measurable (plane f g) :=
  chartMap_measurableEmbedding.measurable_extend
    (ENNReal.measurable_ofReal.comp ((continuous_im.pow _).mul
      ((ModularFormClass.holo (frameForm N (NeZero.pos N) r f g)).continuous.norm.pow 2)).measurable)
    measurable_const

private theorem plane_at {N r : ℕ} [NeZero N] (f : Forms N r) (g : SL(2,ℤ)) (w : ℍ) :
    plane f g (chartMap w)=frameEnergy f g w :=
  chartMap_measurableEmbedding.injective.extend_apply _ _ _

private theorem fiber_mass {N r : ℕ} [NeZero N] (f : Forms N r) (g : SL(2,ℤ))
    (m : ℕ) {y : ℝ} (hy : 0<y) :
    ENNReal.ofReal (y^(2*r)*Real.exp (-(4*Real.pi*m*y))*‖raw N (NeZero.pos N) r g m f‖^2) ≤
      ∫⁻ x,plane f g (x,y) ∂unitMeasure := by
  let u := fun x => ‖frameForm N (NeZero.pos N) r f g (point x y hy)‖^2
  have hu : Continuous u := (((ModularFormClass.holo _).continuous.comp (point_cont y hy)).norm).pow 2
  have hi : Integrable u unitMeasure := (hu.integrableOn_compact isCompact_Icc).mono_set Ico_subset_Icc_self
  have h := ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left (horizontal_square N r f g m hy) (pow_nonneg hy.le (2*r)))
  rw [←mul_assoc] at h
  apply h.trans_eq
  change ENNReal.ofReal (y^(2*r)*∫ x,u x ∂unitMeasure)=_
  rw [←integral_const_mul,ofReal_integral_eq_lintegral_ofReal (hi.const_mul _) (ae_of_all _ fun _ => by dsimp [u];positivity)]
  apply lintegral_congr
  intro x
  have hp : chartMap (point x y hy)=(x,y) := by ext <;>simp [point,chartMap]
  rw [←hp,plane_at]
  simp [frameEnergy,u,point]

theorem strip_fourier_mass (N r : ℕ) [NeZero N] (hr : 0<r) (f : Forms N r)
    (g : SL(2,ℤ)) (m : ℕ) :
    let A := ‖raw N (NeZero.pos N) r g m f‖^2
    (∫⁻ y in Ici (1:ℝ),ENNReal.ofReal (y^(2*r-2)*Real.exp (-(4*Real.pi*m*y))*A)) ≤
      ∫⁻ w in highWidthStrip 1 1,frameEnergy f g w := by
  letI : SigmaFinite verticalWeightedMeasure := by unfold verticalWeightedMeasure;infer_instance
  let A := ‖raw N (NeZero.pos N) r g m f‖^2
  let B := fun y : ℝ => ENNReal.ofReal (y^(2*r)*Real.exp (-(4*Real.pi*m*y))*A)
  have Bm : Measurable B := by dsimp [B];fun_prop
  have mapE := (chartMap_measurableEmbedding.lintegral_map
    (μ:=(volume : Measure ℍ).restrict (highWidthStrip 1 1)) (plane f g))
  rw [highStrip_chart_map_measure,lintegral_prod_symm _ (plane_meas f g).aemeasurable] at mapE
  simp_rw [plane_at] at mapE
  apply le_trans _ mapE.le
  calc
    _ = ∫⁻ y in Ici (1:ℝ),B y ∂verticalWeightedMeasure := by
      unfold verticalWeightedMeasure
      rw [setLIntegral_withDensity_eq_setLIntegral_mul _ verticalWeight_measurable.coe_nnreal_ennreal
        Bm measurableSet_Ici,Measure.restrict_restrict measurableSet_Ici,
        inter_eq_left.mpr (show Ici (1:ℝ)⊆Ioi 0 from fun _ hy => lt_of_lt_of_le zero_lt_one hy)]
      apply setLIntegral_congr_fun measurableSet_Ici
      intro y hy
      have yp : 0<y := lt_of_lt_of_le zero_lt_one hy
      have w : (verticalWeight y:ℝ≥0∞)=ENNReal.ofReal ((y⁻¹)^2) := by
        rw [verticalWeight,ENNReal.ofReal_eq_coe_nnreal (sq_nonneg _)]
      change _=(verticalWeight y:ℝ≥0∞)*B y
      rw [w,B,←ENNReal.ofReal_mul (sq_nonneg _)]
      apply congrArg ENNReal.ofReal
      have powers : y^(2*r)=y^(2*r-2)*y^2 := by rw [←pow_add];congr 1 <;>omega
      rw [powers]
      field_simp [yp.ne'] <;>ring
    _ ≤ _ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ici] with y hy
      exact fiber_mass f g m (lt_of_lt_of_le zero_lt_one hy)

end ImbalancedChen.Part3.OriginalHighStripFourierMass20261112
end
