import ImbalancedChen.Part3OriginalRegularPreKuznetsovProbe
import Batteries.Tactic.OpenPrivate
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! The Gaussian r² average of the exponential pre-Kuznetsov probe.
The same absolute constant works on every dyadic shell and at either
sign of the real spectral order. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalRegularPreKuznetsovGaussian20261113
open Set MeasureTheory Complex
open OriginalRegularPreKuznetsovProbe20261113 (probe positive_half_gamma_norm)
open private cosh_compare from ImbalancedChen.Part3ActualUnitBandMellinProbe

private theorem cosh_product_abs (t r : ℝ) :
    Real.cosh (Real.pi*(|t|-r))*Real.cosh (Real.pi*(|t|+r))=
    Real.cosh (Real.pi*(t-r))*Real.cosh (Real.pi*(t+r)) := by
  rcases le_total 0 t with h|h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h,show Real.pi*(-t-r)= -(Real.pi*(t+r)) by ring,
      show Real.pi*(-t+r)= -(Real.pi*(t-r)) by ring,Real.cosh_neg,Real.cosh_neg,mul_comm]

private theorem cosh_product_near {t r : ℝ} (d : | |t|-r |≤1) :
    Real.cosh (Real.pi*(t-r))*Real.cosh (Real.pi*(t+r))≤
      2*Real.exp Real.pi*Real.cosh (Real.pi*t)*Real.cosh (Real.pi*r) := by
  let a := Real.pi*|t|
  let b := Real.pi*r
  have e : Real.cosh a=Real.cosh (Real.pi*t) := by
    rw [show a=|Real.pi*t| by dsimp only [a]; rw [abs_mul,abs_of_pos Real.pi_pos],Real.cosh_abs]
  have dist : |(a-b)-0|≤Real.pi := by
    dsimp only [a,b]
    rw [sub_zero,←mul_sub,abs_mul,abs_of_pos Real.pi_pos]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left d Real.pi_pos.le
  have lo := cosh_compare dist
  rw [Real.cosh_zero,mul_one] at lo
  have hi : Real.cosh (a+b)≤2*Real.cosh a*Real.cosh b := by
    have z := (Real.cosh_pos (a-b)).le
    rw [Real.cosh_sub] at z
    rw [Real.cosh_add]
    linarith only [z]
  rw [←cosh_product_abs t r,mul_sub,mul_add,←e]
  change Real.cosh (a-b)*Real.cosh (a+b)≤2*Real.exp Real.pi*Real.cosh a*Real.cosh b
  calc
    _ ≤ Real.exp Real.pi*(2*Real.cosh a*Real.cosh b) :=
      mul_le_mul lo hi (Real.cosh_pos _).le (Real.exp_pos _).le
    _ = _ := by ring

private theorem near_floor :
    ∃ C : ℝ,0<C ∧ ∀ {r t : ℝ},1≤r → | |t|-r |≤1 →
      (Real.cosh (Real.pi*t))⁻¹≤C*r*‖probe r ((t:ℂ)*I)‖^2 := by
  let C := 8*Real.exp Real.pi*Real.cosh Real.pi/(Real.pi^3*Real.sinh Real.pi)
  have p := Real.pi_pos
  have sh := Real.sinh_pos_iff.mpr p
  have cp := Real.cosh_pos Real.pi
  have ep := Real.exp_pos Real.pi
  refine ⟨C,by dsimp only [C]; positivity,?_⟩
  intro r t r1 d
  have r0 := zero_lt_one.trans_le r1
  let D := Real.cosh (Real.pi*(t-r))*Real.cosh (Real.pi*(t+r))
  have d0 : 0<D := mul_pos (Real.cosh_pos _) (Real.cosh_pos _)
  have dr : D≤2*Real.exp Real.pi*Real.cosh (Real.pi*t)*Real.cosh (Real.pi*r) := cosh_product_near d
  have atR := Real.sinh_nonneg_iff.mpr (show 0≤Real.pi*r-Real.pi by
    nlinarith only [mul_le_mul_of_nonneg_left r1 p.le])
  rw [Real.sinh_sub] at atR
  have ratio : Real.cosh (Real.pi*r)*Real.sinh Real.pi≤Real.cosh Real.pi*Real.sinh (Real.pi*r) := by
    linarith only [atR]
  have denom : D*Real.sinh Real.pi≤
       2*Real.exp Real.pi*Real.cosh (Real.pi*t)*Real.cosh Real.pi*Real.sinh (Real.pi*r) := by
    have h1 := mul_le_mul_of_nonneg_right dr sh.le
    have h2 := mul_le_mul_of_nonneg_left ratio
      (show 0≤2*Real.exp Real.pi*Real.cosh (Real.pi*t) by positivity)
    nlinarith only [h1,h2]
  rw [positive_half_gamma_norm r0]
  change (Real.cosh (Real.pi*t))⁻¹≤C*r*((Real.pi^3/4)*Real.sinh (Real.pi*r)/(r*D))
  calc
    _ ≤ 2*Real.exp Real.pi*Real.cosh Real.pi*Real.sinh (Real.pi*r)/(D*Real.sinh Real.pi) := by
      rw [inv_eq_one_div,div_le_div_iff₀ (Real.cosh_pos _) (mul_pos d0 sh)]
      linarith only [denom]
    _ = _ := by
      dsimp only [C]
      field_simp [d0.ne',sh.ne',r0.ne',p.ne'] <;> ring

def weight (K r : ℝ) : ℝ := r^2*Real.exp (-(r/K)^2)

def mass (K t r : ℝ) : ℝ := weight K r*‖probe r ((t:ℂ)*I)‖^2

theorem weight_nonnegative (K r : ℝ) : 0≤weight K r :=
  mul_nonneg (sq_nonneg _) (Real.exp_pos _).le

theorem mass_nonnegative (K t r : ℝ) : 0≤mass K t r :=
  mul_nonneg (weight_nonnegative K r) (sq_nonneg _)

private theorem density_eq {r : ℝ} (hr : 0<r) (K t : ℝ) :
    mass K t r=(Real.pi^3/4)*r*Real.exp (-(r/K)^2)*Real.sinh (Real.pi*r)/
      (Real.cosh (Real.pi*(t-r))*Real.cosh (Real.pi*(t+r))) := by
  rw [mass,weight,positive_half_gamma_norm hr]
  field_simp [hr.ne',(Real.cosh_pos (Real.pi*(t-r))).ne',(Real.cosh_pos (Real.pi*(t+r))).ne'] <;> ring

private theorem mass_cont (K t : ℝ) : ContinuousOn (mass K t) (Ioi 0) := by
  let f := fun r : ℝ => (Real.pi^3/4)*r*Real.exp (-(r/K)^2)*Real.sinh (Real.pi*r)/
    (Real.cosh (Real.pi*(t-r))*Real.cosh (Real.pi*(t+r)))
  have cf : Continuous f := by
    dsimp only [f]
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro r
      exact (mul_pos (Real.cosh_pos _) (Real.cosh_pos _)).ne'
  exact cf.continuousOn.congr (fun r hr => density_eq hr K t)

private theorem denominator_large (r t : ℝ) (hr : 0≤r) :
    Real.sinh (Real.pi*r)≤2*(Real.cosh (Real.pi*(t-r))*Real.cosh (Real.pi*(t+r))) := by
  let a := Real.pi*(t-r)
  let b := Real.pi*(t+r)
  have id : 2*(Real.cosh a*Real.cosh b)=Real.cosh (a+b)+Real.cosh (b-a) := by
    rw [Real.cosh_add,Real.cosh_sub]
    ring
  have h : Real.cosh (Real.pi*r)≤Real.cosh (b-a) := by
    rw [show b-a=Real.pi*r+Real.pi*r by dsimp only [a,b]; ring]
    apply Real.cosh_le_cosh.mpr
    rw [abs_of_nonneg (mul_nonneg Real.pi_pos.le hr),abs_of_nonneg (by positivity)]
    linarith only [mul_nonneg Real.pi_pos.le hr]
  have s : Real.sinh (Real.pi*r)≤Real.cosh (Real.pi*r) := by
    rw [Real.sinh_eq,Real.cosh_eq]
    linarith only [(Real.exp_pos (-(Real.pi*r))).le]
  change _ ≤ 2*(Real.cosh a*Real.cosh b)
  rw [id]
  linarith only [s,h,(Real.cosh_pos (a+b)).le]

theorem mass_integrable {K : ℝ} (hK : 0<K) (t : ℝ) : IntegrableOn (mass K t) (Ioi 0) := by
  have hβ : 0<(K^2)⁻¹ := inv_pos.mpr (sq_pos_of_pos hK)
  have g := integrableOn_rpow_mul_exp_neg_mul_rpow (p:=(2:ℝ)) (s:=(1:ℝ)) (b:=(K^2)⁻¹)
    (by norm_num) (by norm_num) hβ
  have exponent (r : ℝ) : -(r/K)^2= -((K^2)⁻¹)*r^2 := by rw [div_pow,div_eq_inv_mul]; ring
  have gb : IntegrableOn (fun r : ℝ => (Real.pi^3/4*2)*(r*Real.exp (-(r/K)^2))) (Ioi 0) := by
    simpa only [exponent,Real.rpow_one,Real.rpow_two,neg_mul] using g.const_mul (Real.pi^3/4*2)
  apply gb.mono' ((mass_cont K t).aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem (μ:=volume) (measurableSet_Ioi : MeasurableSet (Ioi (0:ℝ)))] with r hr
  rw [Real.norm_of_nonneg (mass_nonnegative K t r),density_eq hr K t]
  have D0 := mul_pos (Real.cosh_pos (Real.pi*(t-r))) (Real.cosh_pos (Real.pi*(t+r)))
  rw [div_le_iff₀ D0]
  have h := mul_le_mul_of_nonneg_left (denominator_large r t hr.le)
    (show 0≤(Real.pi^3/4)*r*Real.exp (-(r/K)^2) by positivity)
  linarith only [h]

/-- The original positive full half-line Gaussian average dominates every
regular real-order weight in the shell. Dividing the resulting trace
bound by K is uniform in the shell. -/
theorem dyadic_gaussian_majorant :
    ∃ C : ℝ,0<C ∧ ∀ {K t : ℝ}, 2≤|t| → K/2≤|t| → |t|≤K →
      K*(Real.cosh (Real.pi*t))⁻¹ ≤ C*∫ r in Ioi (0:ℝ),mass K t r := by
  obtain ⟨C,hC,floor⟩ := near_floor
  let D := 4*C*Real.exp 1
  refine ⟨D,by dsimp only [D]; positivity,?_⟩
  intro K t ht hlo hhi
  let a := |t|-1
  let b := |t|
  have ap : 0<a := by dsimp only [a]; linarith
  have ab : a≤b := by dsimp only [a,b]; linarith
  have K0 : 0<K := by linarith
  have step : b-a=1 := by dsimp only [a,b]; ring
  have ib := ((mass_cont K t).mono (show uIcc a b⊆Ioi 0 by
    rw [uIcc_of_le ab]; exact fun _ hr => ap.trans_le hr.1)).intervalIntegrable
  have grow : (∫ r in a..b,mass K t r)≤∫ r in Ioi (0:ℝ),mass K t r := by
    rw [intervalIntegral.integral_of_le ab]
    exact setIntegral_mono_set (mass_integrable K0 t) (ae_of_all _ (mass_nonnegative K t))
      (ae_of_all _ (fun _ hr => ap.trans hr.1))
  calc
    _ = ∫ _r in a..b,K*(Real.cosh (Real.pi*t))⁻¹ := by
      rw [intervalIntegral.integral_const,step,one_smul]
    _ ≤ ∫ r in a..b,D*mass K t r := by
      apply intervalIntegral.integral_mono_on ab intervalIntegrable_const (ib.const_mul D)
      intro r hr
      have r1 : 1≤r := by dsimp only [a] at hr; linarith [hr.1]
      have r0 := zero_lt_one.trans_le r1
      have dt : | |t|-r |≤1 := abs_le.mpr ⟨by dsimp only [b] at hr; linarith [hr.2],
        by dsimp only [a] at hr; linarith [hr.1]⟩
      have rK : r≤K := hr.2.trans hhi
      have Kr : K≤4*r := by dsimp only [a] at hr; linarith [hr.1]
      have q0 := (div_nonneg r0.le K0.le)
      have q1 := (div_le_one K0).mpr rK
      have g : 1≤Real.exp 1*Real.exp (-(r/K)^2) := by
        rw [←Real.exp_add,Real.one_le_exp_iff]
        nlinarith only [mul_nonneg q0 (sub_nonneg.mpr q1),q1]
      have scale : K*(C*r)≤D*weight K r := by
        have h1 := mul_le_mul_of_nonneg_right Kr (mul_nonneg hC.le r0.le)
        have h2 := mul_le_mul_of_nonneg_left g (show 0≤4*C*r^2 by positivity)
        dsimp only [D,weight]
        nlinarith only [h1,h2]
      calc
        _ ≤ K*(C*r*‖probe r ((t:ℂ)*I)‖^2) := mul_le_mul_of_nonneg_left (floor r1 dt) K0.le
        _ ≤ D*mass K t r := by
          have h := mul_le_mul_of_nonneg_right scale (sq_nonneg ‖probe r ((t:ℂ)*I)‖)
          dsimp only [mass]; linarith only [h]
    _ = D*(∫ r in a..b,mass K t r) := intervalIntegral.integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left grow (by dsimp only [D]; positivity)

end ImbalancedChen.Part3.OriginalRegularPreKuznetsovGaussian20261113
end

