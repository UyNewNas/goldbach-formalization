import ImbalancedChen.Part3OriginalRegularPreKuznetsovPolar
import ImbalancedChen.Part3ActualKTransformFourier
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Prod

/-! Absolute integrability in the upper semicircle and logarithmic radius.
The long-modulus majorant for positive regularization retains the extra
power supplied by the regularizing product. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalRegularPreKuznetsovOrbitL120261113
open Set Filter MeasureTheory Complex
open OriginalRegularPreKuznetsovAngle20261113 (angularWave angular angular_wave_norm)
open OriginalRegularPreKuznetsovFourier20261113 (character)
open ActualKTransformFourier20261024z (exp_neg_abs_integrable)

def angleMeasure : Measure ℝ := volume.restrict (Ioo 0 Real.pi)

def angleMass (u : ℝ) := ∫ θ in (0:ℝ)..Real.pi,Real.exp (-u*Real.sin θ)

private theorem exp_half (u : ℝ) (hu : 0<u) :
    (∫ θ in (0:ℝ)..Real.pi/2,Real.exp (-u*Real.sin θ))≤Real.pi/(2*u) := by
  let b := u*(2/Real.pi)
  have b0 : 0<b := mul_pos hu (div_pos (by norm_num) Real.pi_pos)
  have p := (half_pos Real.pi_pos).le
  have g : IntegrableOn (fun θ : ℝ => Real.exp (-b*θ)) (Ioi 0) := integrableOn_exp_mul_Ioi (neg_lt_zero.mpr b0) 0
  calc
    _ ≤ ∫ θ in (0:ℝ)..Real.pi/2,Real.exp (-b*θ) := by
      apply intervalIntegral.integral_mono_on p
        ((show Continuous (fun θ : ℝ => Real.exp (-u*Real.sin θ)) by fun_prop).intervalIntegrable _ _)
        ((show Continuous (fun θ : ℝ => Real.exp (-b*θ)) by fun_prop).intervalIntegrable _ _)
      intro θ hθ
      apply Real.exp_le_exp.mpr
      have d := mul_le_mul_of_nonneg_left (Real.mul_le_sin hθ.1 hθ.2) hu.le
      dsimp only [b]; linarith only [d]
    _ ≤ ∫ θ in Ioi (0:ℝ),Real.exp (-b*θ) := by
      rw [intervalIntegral.integral_of_le p]
      exact setIntegral_mono_set g (ae_of_all _ (fun θ => (Real.exp_pos _).le))
        (ae_of_all _ (fun _ h => h.1))
    _ = _ := by
      rw [integral_exp_mul_Ioi (neg_lt_zero.mpr b0) 0,mul_zero,Real.exp_zero]
      dsimp only [b];field_simp [Real.pi_ne_zero,hu.ne'] <;> ring

theorem angle_mass_bound {u : ℝ} (hu : 0<u) : angleMass u≤Real.pi/u := by
  let f := fun θ : ℝ => Real.exp (-u*Real.sin θ)
  have c : Continuous f := by dsimp only [f]; fun_prop
  have flip := intervalIntegral.integral_comp_sub_left (a:=Real.pi/2) (b:=Real.pi) f Real.pi
  have symmetry (θ : ℝ) : f (Real.pi-θ)=f θ := by simp only [f,Real.sin_pi_sub]
  simp only [symmetry,sub_self,show Real.pi-Real.pi/2=Real.pi/2 by ring] at flip
  have sum := intervalIntegral.integral_add_adjacent_intervals (c.intervalIntegrable 0 (Real.pi/2))
    (c.intervalIntegrable (Real.pi/2) Real.pi)
  have h : (∫ θ in 0..Real.pi/2,f θ)≤Real.pi/(2*u) := exp_half u hu
  change (∫ θ in 0..Real.pi,f θ)≤_
  have hscale : 2*(Real.pi/(2*u))=Real.pi/u := by field_simp [hu.ne'] <;> ring
  linarith only [flip,sum,h,hscale]

theorem angle_mass_trivial {u : ℝ} (hu : 0≤u) : angleMass u≤Real.pi := by
  let f := fun θ : ℝ => Real.exp (-u*Real.sin θ)
  have h := intervalIntegral.integral_mono_on Real.pi_pos.le
    ((show Continuous f by dsimp only [f];fun_prop).intervalIntegrable 0 Real.pi)
    (intervalIntegrable_const (c:=(1:ℝ))) (fun θ hθ => (Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hu) (Real.sin_nonneg_of_mem_Icc hθ))))
  simpa only [angleMass,f,intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_one] using h

theorem integral_norm (u : ℝ) : (∫ θ,‖angularWave u θ‖ ∂angleMeasure)=angleMass u := by
  simp_rw [angular_wave_norm]
  rw [angleMass,intervalIntegral.integral_of_le Real.pi_pos.le,integral_Ioc_eq_integral_Ioo] <;> rfl

theorem sech_exp (ξ : ℝ) : (Real.cosh ξ)⁻¹≤2*Real.exp (-|ξ|) := by
  rw [←Real.cosh_abs ξ,Real.exp_neg]
  have c := Real.cosh_pos |ξ|
  have e := Real.exp_pos |ξ|
  rw [inv_eq_one_div,inv_eq_one_div,mul_one_div,div_le_div_iff₀ c e,one_mul]
  rw [Real.cosh_eq]
  linarith only [(Real.exp_pos (-|ξ|)).le]

def polarWave (δ u r ξ θ : ℝ) : ℂ :=
  ((Real.sin θ^(2*δ):ℝ):ℂ)*character ξ r*angularWave (u*Real.cosh ξ) θ

private theorem polar_norm {δ : ℝ} (d0 : 0≤δ) (u r ξ : ℝ) {θ : ℝ} (hθ : θ∈Icc 0 Real.pi) :
    ‖polarWave δ u r ξ θ‖≤‖angularWave (u*Real.cosh ξ) θ‖ := by
  have sin0 := Real.sin_nonneg_of_mem_Icc hθ
  have pow0 := Real.rpow_nonneg sin0 (2*δ)
  have pow1 := Real.rpow_le_one sin0 (Real.sin_le_one θ) (by positivity : 0≤2*δ)
  have w : ‖character ξ r‖=1 := by simp [character,Complex.norm_exp,Complex.mul_re,Complex.mul_im]
  simp only [polarWave,norm_mul,Complex.norm_real,Real.norm_of_nonneg pow0,w,mul_one]
  exact mul_le_of_le_one_left (norm_nonneg _) pow1

theorem polar_integrable {δ u : ℝ} (d0 : 0≤δ) (hu : 0<u) (r : ℝ) :
    Integrable (Function.uncurry (polarWave δ u r)) (volume.prod angleMeasure) := by
  let f := polarWave δ u r
  have M : Measurable (Function.uncurry f) := by
    unfold f polarWave Function.uncurry angularWave OriginalRegularPreKuznetsovAngle20261113.ray character
    fun_prop
  apply (integrable_prod_iff M.aestronglyMeasurable).mpr
  have m (ξ : ℝ) : Integrable (fun θ => angularWave (u*Real.cosh ξ) θ) angleMeasure :=
    ((show Continuous (angularWave (u*Real.cosh ξ)) by
      unfold angularWave OriginalRegularPreKuznetsovAngle20261113.ray;fun_prop).continuousOn.integrableOn_compact
      (isCompact_Icc (a:=(0:ℝ)) (b:=Real.pi))).mono_set Ioo_subset_Icc_self
  have row (ξ : ℝ) : Integrable (f ξ) angleMeasure := by
    apply (m ξ).norm.mono'
      (show Measurable (f ξ) by unfold f polarWave angularWave OriginalRegularPreKuznetsovAngle20261113.ray character; fun_prop).aestronglyMeasurable
    filter_upwards [ae_restrict_mem (μ:=volume) (measurableSet_Ioo : MeasurableSet (Ioo (0:ℝ) Real.pi))] with θ hθ
    exact polar_norm d0 u r ξ ⟨hθ.1.le,hθ.2.le⟩
  refine ⟨ae_of_all _ row,?_⟩
  have major := (exp_neg_abs_integrable (b:=(1:ℝ)) (by norm_num)).const_mul (2*Real.pi/u)
  apply major.mono' M.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
  filter_upwards with ξ
  change ‖∫ θ,‖f ξ θ‖ ∂angleMeasure‖≤(2*Real.pi/u)*Real.exp (-1*|ξ|)
  rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _)),neg_one_mul]
  calc
    _ ≤ ∫ θ,‖angularWave (u*Real.cosh ξ) θ‖ ∂angleMeasure := by
      apply integral_mono_ae (row ξ).norm (m ξ).norm
      filter_upwards [ae_restrict_mem (μ:=volume) (measurableSet_Ioo : MeasurableSet (Ioo (0:ℝ) Real.pi))] with θ hθ
      exact polar_norm d0 u r ξ ⟨hθ.1.le,hθ.2.le⟩
    _ = angleMass (u*Real.cosh ξ) := integral_norm _
    _ ≤ Real.pi/(u*Real.cosh ξ) := angle_mass_bound (mul_pos hu (Real.cosh_pos _))
    _ ≤ _ := by
      have factor := mul_le_mul_of_nonneg_left (sech_exp ξ) (div_nonneg Real.pi_pos.le hu.le)
      convert factor using 1 <;> ring

end ImbalancedChen.Part3.OriginalRegularPreKuznetsovOrbitL120261113
end
