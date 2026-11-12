import ImbalancedChen.Part3OriginalPeterssonNormalization
import ImbalancedChen.Part3ActualPoincareSpectralCoefficient
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace ImbalancedChen.Part3.OriginalHeckeStripPairing20261112

noncomputable section
open Set MeasureTheory Filter Complex UpperHalfPlane
open scoped MatrixGroups ModularForm UpperHalfPlane ComplexConjugate
open GammaInfinityTranslationStrip20261025a Gamma0ActualParabolicUnfolding20261025a
open Gamma0FiniteMeasureCarrier20261024z Gamma0CarrierAESection20261025a
open ActualPoincareSpectralCoefficient20261026a CanonicalPlanarL2UnitarySourceOnly
open CanonicalTensorHyperbolicLaplacianForm20261024z MaassWeightedCoordinateL220261024zz
open OriginalHolomorphicCuspFrames20261110 OriginalPeterssonPretrace20261112
open OriginalHolomorphicPeterssonSpace20261112 NativeHolomorphicFourierNormalization20261102s

def q (w : ℍ) : ℂ := Function.Periodic.qParam 1 (w:ℂ)

theorem q_norm (w : ℍ) (m : ℕ) :
    ‖q w ^ m‖ = Real.exp (-(2*Real.pi*m*w.im)) := by
  rw [norm_pow, q, Function.Periodic.norm_qParam, div_one, ← Real.exp_nat_mul]
  congr 1; ring

theorem q_conjugate (w : ℍ) (m : ℕ) :
    conj (q w ^ m) = (Real.exp (-(4*Real.pi*m*w.im)) : ℂ) / q w ^ m := by
  rw [eq_div_iff (pow_ne_zero _ (Function.Periodic.qParam_ne_zero 1 _)), mul_comm,
    Complex.mul_conj, Complex.normSq_eq_norm_sq, q_norm, ← Real.exp_nat_mul]
  congr 2; push_cast; ring

def weightSeed {N r : ℕ} (f : Forms N r) (m : ℕ) (s : ℝ) (w : ℍ) : ℂ :=
  ((w.im ^ (2*(r:ℝ)+s) : ℝ) : ℂ) * conj (q w ^ m) * f w

private theorem seed_continuous {N r : ℕ} (f : Forms N r) (m : ℕ) (s : ℝ) :
    Continuous (weightSeed f m s) := by
  unfold weightSeed q
  exact ((Complex.continuous_ofReal.comp (continuous_im.rpow_const (fun w => .inl w.im_ne_zero))).mul
    (((Function.Periodic.continuous_qParam 1).comp continuous_coe).pow m).star).mul
    (ModularFormClass.holo f).continuous

theorem q_translate (l : ℤ) (w : ℍ) : q (translate l w)=q w := by
  rw [q,q,translate_eq_vadd]
  simp only [UpperHalfPlane.coe_vadd, Complex.ofReal_intCast, Function.Periodic.qParam, div_one]
  rw [show 2*(Real.pi:ℂ)*I*((l:ℂ)+(w:ℂ))=
    (l:ℂ)*(2*Real.pi*I)+2*Real.pi*I*w by ring, Complex.exp_add, Complex.exp_int_mul,
    Complex.exp_two_pi_mul_I, one_zpow, one_mul]

private theorem seed_periodic {N r : ℕ} (f : Forms N r) (m : ℕ) (s : ℝ) (l : ℤ) (w : ℍ) :
    weightSeed f m s (translate l w)=weightSeed f m s w := by
  have hT : f (translate l w) = f w := by
    have h := SlashInvariantFormClass.slash_action_eq f _
      (show Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T^l) ∈ levelGroup N from
        Subgroup.mem_map.mpr ⟨_, Gamma0ActualCuspsSourceOnly.translation_mem_gamma0 N l, rfl⟩)
    have h' := congrFun h w
    simpa [translate, ModularForm.slash_apply, UpperHalfPlane.σ, UpperHalfPlane.denom_apply,
      ModularGroup.coe_T_zpow] using h'
  have hm : (translate l w).im=w.im := by rw [translate_eq_vadd]; rfl
  simp only [weightSeed,hm,hT,q_translate]

def planar {N r : ℕ} (f : Forms N r) (m : ℕ) (s : ℝ) : ℝ×ℝ → ℂ :=
  Function.extend chartMap (strip.indicator (weightSeed f m s)) 0

private theorem planar_at_chart {N r : ℕ} (f : Forms N r) (m : ℕ) (s : ℝ) (w : ℍ) :
    planar f m s (chartMap w) = strip.indicator (weightSeed f m s) w :=
  chartMap_measurableEmbedding.injective.extend_apply _ _ _

private theorem planar_measurable {N r : ℕ} (f : Forms N r) (m : ℕ) (s : ℝ) :
    Measurable (planar f m s) :=
  chartMap_measurableEmbedding.measurable_extend
    ((seed_continuous f m s).measurable.indicator strip_measurable) measurable_const

private theorem laplace_L1 {a b : ℝ} (ha : 0<a) (hb : 0<b) :
    IntegrableOn (fun y : ℝ => y^(a-1)*Real.exp (-(b*y))) (Ioi 0) := by
  by_contra h
  have H := Real.integral_rpow_mul_exp_neg_mul_Ioi ha hb
  rw [integral_undef h] at H
  exact ((mul_pos (Real.rpow_pos_of_pos (one_div_pos.mpr hb) _) (Real.Gamma_pos_of_pos ha)).ne') H.symm

private theorem vertical_L1 {r m : ℕ} {s : ℝ} (hm : 0<m) (hs : 1<(r:ℝ)+s) (C : ℝ) :
    Integrable (fun y : ℝ => C * (y^((r:ℝ)+s) * Real.exp (-(2*Real.pi*m*y))))
      verticalWeightedMeasure := by
  apply (integrable_withDensity_iff_integrable_smul verticalWeight_measurable).mpr
  apply ((laplace_L1 (a:=(r:ℝ)+s-1) (by linarith) (b:=2*Real.pi*m) (by positivity)).const_mul C).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  change _ = (y⁻¹)^2 * _
  rw [show (y⁻¹)^2=y^(-2:ℝ) by rw [Real.rpow_neg hy.le]; norm_num [inv_pow]]
  rw [show (r:ℝ)+s-1-1=(-2)+((r:ℝ)+s) by ring, Real.rpow_add hy]
  ring

theorem planar_L1 {N r : ℕ} [NeZero N] (f : Forms N r) {m : ℕ} (hm : 0<m)
    {s : ℝ} (hs : 1<(r:ℝ)+s) : Integrable (planar f m s) chartMeasure := by
  letI : SigmaFinite verticalWeightedMeasure := by unfold verticalWeightedMeasure; infer_instance
  obtain ⟨C,hC⟩ := CuspFormClass.exists_bound f
  let H := fun x : ℝ => (Ico (0:ℝ) 1).indicator (fun _ => (1:ℝ)) x
  have hh : Integrable H := (integrable_indicator_iff measurableSet_Ico).mpr
    (integrableOn_const measure_Ico_lt_top.ne)
  rw [chartMeasure_eq_product]
  apply (hh.mul_prod (vertical_L1 hm hs C)).mono' (planar_measurable f m s).aestronglyMeasurable
  have hpos : ∀ᵐ y : ℝ ∂verticalWeightedMeasure, 0<y :=
    (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioi)
  filter_upwards [(Measure.quasiMeasurePreserving_snd (μ:=volume) (ν:=verticalWeightedMeasure)).ae hpos]
    with p hp
  let w : ℍ := ⟨⟨p.1,p.2⟩,hp⟩
  have hw : chartMap w=p := by cases p; rfl
  rw [← hw,planar_at_chart]
  by_cases hx : w.re ∈ Ico (0:ℝ) 1
  · rw [indicator_of_mem (show w∈strip from hx)]
    change _ ≤ H w.re * (C * _)
    rw [show H w.re=1 from indicator_of_mem hx _,one_mul]
    have h := hC w
    rw [show (((2*(r:ℤ):ℤ):ℝ)/2)=(r:ℝ) by push_cast; ring] at h
    have h' := (le_div_iff₀ (Real.rpow_pos_of_pos w.im_pos _)).mp h
    simp only [weightSeed, norm_mul, norm_real, Real.norm_of_nonneg (Real.rpow_nonneg w.im_pos.le _),
      Complex.norm_conj, q_norm]
    rw [show 2*(r:ℝ)+s=((r:ℝ)+s)+(r:ℝ) by ring, Real.rpow_add w.im_pos]
    nlinarith only [mul_le_mul_of_nonneg_left h'
      (mul_nonneg (Real.rpow_nonneg w.im_pos.le ((r:ℝ)+s)) (Real.exp_pos (-(2*Real.pi*m*w.im))).le)]
  · simp [H,strip,hx,chartMap,w] at *

private theorem horizontal {N r : ℕ} [NeZero N] (f : Forms N r) (m : ℕ) (s : ℝ)
    {y : ℝ} (hy : 0<y) :
    (∫ x : ℝ, planar f m s (x,y)) =
      ((y^(2*(r:ℝ)+s)*Real.exp (-(4*Real.pi*m*y)) : ℝ) : ℂ) *
        (qExpansion 1 f).coeff m := by
  let w := fun x : ℝ => (⟨(x:ℂ)+y*I, by simpa using hy⟩ : ℍ)
  have hx (x : ℝ) : chartMap (w x)=(x,y) := by ext <;> simp [w,chartMap]
  have he (x : ℝ) : (w x).im=y := by simp [w]
  let F := fun x : ℝ => 1 / (q (w x))^m * f (w x)
  have hF : (∫ x in (0:ℝ)..1, F x) = (qExpansion 1 f).coeff m := by
    simpa [F,w,q] using
      (ModularFormClass.qExpansion_coeff_eq_intervalIntegral f (by norm_num : (0:ℝ)<1)
        (by simp : (1:ℝ) ∈ (levelGroup N).strictPeriods) m hy).symm
  have heq : (fun x : ℝ => planar f m s (x,y)) = (Ico (0:ℝ) 1).indicator
      (fun x => ((y^(2*(r:ℝ)+s)*Real.exp (-(4*Real.pi*m*y)):ℝ):ℂ)*F x) := by
    funext x
    rw [← hx x,planar_at_chart]
    by_cases h : x∈Ico (0:ℝ) 1
    · have hi : w x∈strip := by simpa [strip,w] using h
      rw [indicator_of_mem hi,indicator_of_mem h,weightSeed,q_conjugate,he]
      simp only [F,Complex.ofReal_mul,div_eq_mul_inv,one_mul]; ring
    · have hi : w x∉strip := by simpa [strip,w] using h
      rw [indicator_of_notMem hi,indicator_of_notMem h]
  rw [heq,integral_indicator measurableSet_Ico,integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),intervalIntegral.integral_const_mul,hF]

def heckeMass (r m : ℕ) (s : ℝ) : ℝ :=
  (1/(4*Real.pi*m))^(2*(r:ℝ)+s-1)*Real.Gamma (2*(r:ℝ)+s-1)

/-- The complete parabolic sum unfolds for every s>0 even at weight two. -/
theorem unfolded (N r : ℕ) [NeZero N] (hr : 0<r) (f : Forms N r) {m : ℕ} (hm : 0<m)
    {s : ℝ} (hs : 0<s) :
    (∫ w in gamma0Carrier N, parabolicTraceComplex N (weightSeed f m s) w) =
      (heckeMass r m s : ℂ) * (qExpansion 1 f).coeff m := by
  letI : SigmaFinite verticalWeightedMeasure := by unfold verticalWeightedMeasure; infer_instance
  have h1 : 1≤(r:ℝ) := by exact_mod_cast hr
  have hi := planar_L1 f hm (by linarith : 1<(r:ℝ)+s)
  have hc : (planar f m s) ∘ chartMap = strip.indicator (weightSeed f m s) :=
    funext (planar_at_chart f m s)
  have hi' := (canonical_complex_integrable_iff_chart _).mpr hi
  rw [hc] at hi'
  have hu := complex_parabolic_carrier_unfolding N _ (seed_periodic f m s)
    (seed_continuous f m s).measurable ((integrable_indicator_iff strip_measurable).mp hi')
  rw [Measure.restrict_congr_set (reducedCarrier_ae_eq_carrier N)] at hu
  rw [hu, ← integral_indicator strip_measurable, ← hc,canonical_complex_integral_eq_chart,
    chartMeasure_eq_product, integral_prod_symm _ (by simpa [chartMeasure_eq_product] using hi)]
  rw [verticalWeightedMeasure, integral_withDensity_eq_integral_smul verticalWeight_measurable]
  let a := 2*(r:ℝ)+s-1
  have ha : 0<a := by dsimp [a]; linarith
  calc
    _ = ∫ y : ℝ in Ioi 0, ((y^(a-1)*Real.exp (-(4*Real.pi*m*y)) : ℝ) : ℂ) *
        (qExpansion 1 f).coeff m := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      rw [horizontal f m s hy]
      change ((y⁻¹)^2 : ℝ) • _ = _
      rw [show (y⁻¹)^2=y^(-2:ℝ) by rw [Real.rpow_neg hy.le]; norm_num [inv_pow]]
      rw [show a-1=(-2)+(2*(r:ℝ)+s) by dsimp [a];ring,Real.rpow_add hy]
      simp [Complex.real_smul,Complex.ofReal_mul,mul_assoc]
    _ = _ := by
      rw [integral_mul_const,integral_ofReal,Real.integral_rpow_mul_exp_neg_mul_Ioi ha
        (by positivity : 0<4*Real.pi*(m:ℝ))]
      rfl

end
end ImbalancedChen.Part3.OriginalHeckeStripPairing20261112
