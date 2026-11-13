import ImbalancedChen.Part3OriginalRegularPreKuznetsovInduced
import Batteries.Tactic.OpenPrivate

/-! A fixed eighth of an angular power is enough to move compact
logarithmic truncation through the physical integer moduli. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalRegularCutoffAngularMass20261113
open Real Set MeasureTheory
open scoped ENNReal
open OriginalRegularPreKuznetsovOrbitL120261113
open OriginalRegularPreKuznetsovAngle20261113 (angularWave)
open OriginalRegularPreKuznetsovFourier20261113 (character)
open ActualKTransformFourier20261024z (exp_neg_abs_integrable)
open private raw raw_meas chart_mass slot_int angularSlot angleFull coeff from ImbalancedChen.Part3OriginalRegularPreKuznetsovInduced

def tilt : ℝ := 1/8
theorem tilt_pos : 0<tilt := by norm_num [tilt]
theorem tilt_lt_quarter : tilt<1/4 := by norm_num [tilt]

def angleConstant := π*(2:ℝ)^tilt*(∫ ξ : ℝ,exp (-tilt*|ξ|))

theorem angleConstant_nonnegative : 0≤angleConstant := by
  apply mul_nonneg (mul_nonneg pi_pos.le (rpow_nonneg (by norm_num) _))
  exact integral_nonneg (fun ξ => (exp_pos _).le)

private theorem tilt_bound {v : ℝ} (hv : 0<v) : angleMass v≤π*v^(-tilt) := by
  by_cases small : v≤1
  · have g := one_le_rpow_of_pos_of_le_one_of_nonpos hv small (neg_nonpos.mpr tilt_pos.le)
    exact (angle_mass_trivial hv.le).trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left g pi_pos.le)
  · have g := rpow_le_rpow_of_exponent_le (le_of_not_ge small)
      (show (-1:ℝ)≤ -tilt by norm_num [tilt])
    rw [rpow_neg_one] at g
    exact (angle_mass_bound hv).trans (by simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left g pi_pos.le)

private theorem tilt_cosh (ξ : ℝ) : cosh ξ^(-tilt)≤(2:ℝ)^tilt*exp (-tilt*|ξ|) := by
  have h := rpow_le_rpow (inv_nonneg.mpr (cosh_pos _).le) (sech_exp ξ) tilt_pos.le
  rw [←rpow_neg_eq_inv_rpow,mul_rpow (by norm_num) (exp_pos _).le,
    ←Real.exp_mul,show -|ξ|*tilt= -tilt*|ξ| by ring] at h
  exact h

theorem mass_integrable {u : ℝ} (hu : 0<u) : Integrable (fun ξ : ℝ => angleMass (u*cosh ξ)) := by
  let V := Function.uncurry (polarWave 0 u 0)
  have E (ξ θ : ℝ) : ‖V (ξ,θ)‖=‖angularWave (u*cosh ξ) θ‖ := by
    simp only [V,Function.uncurry,polarWave,mul_zero,rpow_zero,Complex.ofReal_one,one_mul,
      character,Complex.ofReal_zero,zero_mul,Complex.exp_zero]
  have a := (polar_integrable (le_refl 0) hu 0).norm.integral_prod_left
  apply a.congr
  filter_upwards with ξ
  change (∫ θ,‖V (ξ,θ)‖ ∂angleMeasure)=_
  simp_rw [E]
  exact integral_norm _

theorem angular_price {u : ℝ} (hu : 0<u) :
    (∫ ξ : ℝ,angleMass (u*cosh ξ))≤angleConstant*u^(-tilt) := by
  have w := exp_neg_abs_integrable tilt_pos
  have bound (ξ : ℝ) :
      angleMass (u*cosh ξ)≤(π*u^(-tilt)*(2:ℝ)^tilt)*exp (-tilt*|ξ|) := by
    have p := tilt_bound (mul_pos hu (cosh_pos ξ))
    rw [Real.mul_rpow hu.le (cosh_pos _).le] at p
    have q := mul_le_mul_of_nonneg_left (tilt_cosh ξ) (mul_nonneg pi_pos.le (rpow_nonneg hu.le _))
    nlinarith only [p,q]
  have h := integral_mono (mass_integrable hu) (w.const_mul (π*u^(-tilt)*(2:ℝ)^tilt)) bound
  rw [integral_const_mul] at h
  unfold angleConstant
  nlinarith only [h]

theorem raw_integrable {p : ℝ} (hp : 0<p) (r : ℝ) : Integrable (raw 0 p r) := by
  refine ⟨(raw_meas 0 p r).aestronglyMeasurable,?_⟩
  rw [hasFiniteIntegral_iff_enorm,chart_mass hp r]
  exact (slot_int hp (le_refl 0) r).lintegral_lt_top

private theorem slot_norm (p r ξ : ℝ) :
    (∫ θ,‖angularSlot 0 p r ξ θ‖ ∂angleFull)=π^2*p^2*angleMass (4*π*p*cosh ξ) := by
  have ch : ‖character ξ r‖=1 := by simp [character,Complex.norm_exp,Complex.mul_re,Complex.mul_im]
  simp only [angularSlot,norm_mul,norm_indicator_eq_indicator_norm,Complex.norm_real,Real.norm_eq_abs,
    coeff,rpow_zero,mul_one,abs_of_nonneg (mul_nonneg (sq_nonneg π) (sq_nonneg p)),
    polarWave,mul_zero,Complex.ofReal_one,one_mul,norm_mul,ch]
  rw [integral_const_mul]
  congr 1
  change (∫ θ in Ioo (-π) π,(Ioo (0:ℝ) π).indicator _ θ)=_
  rw [setIntegral_indicator measurableSet_Ioo]
  have sub : Ioo (0:ℝ) π⊆Ioo (-π) π := fun _ ht => ⟨(neg_lt_zero.mpr pi_pos).trans ht.1,ht.2⟩
  simp only [inter_eq_right.mpr sub,inter_eq_left.mpr sub]
  exact integral_norm _

theorem raw_mass {p : ℝ} (hp : 0<p) (r : ℝ) :
    (∫ z : ℝ×ℝ,‖raw 0 p r z‖)=π^2*p^2*∫ ξ : ℝ,angleMass (4*π*p*cosh ξ) := by
  have row := slot_int hp (le_refl 0) r
  rw [integral_norm_eq_lintegral_enorm (raw_integrable hp r).aestronglyMeasurable,
    chart_mass hp r,←integral_norm_eq_lintegral_enorm row.aestronglyMeasurable,
    integral_prod _ row.norm]
  simp only [Function.uncurry,slot_norm,integral_const_mul]

end ImbalancedChen.Part3.OriginalRegularCutoffAngularMass20261113
end

