import ImbalancedChen.Part3OriginalPositiveScalarGeometry
import ImbalancedChen.Part3OriginalPositiveStripThreshold
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Batteries.Tactic.OpenPrivate

/-! A single small-argument price for all of the actual ratio windows. Its
integrable bound is translated by log q; this retains the weight-two tail. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalPositiveScalarGeometry20261112
open Set Filter MeasureTheory Complex
open scoped BigOperators Topology
open P3NativePeriod64SamplingSourceOnly (D4)
open RadialSchrodingerL2Form20261025a (RadialTest)
open OriginalPositiveRatioWindows20261112 (ratio ratio_zero ratio_pointwise ratio_jets)
open OriginalPositiveStrip20261112 (h residual original_projection smooth)
open OriginalPositiveStripDensity20261112 (h_jets)
open private abs_exp_integrable from ImbalancedChen.Part3OriginalPositiveStripContour

def response (H : RadialTest) (q : ℝ) := ∫ w : ℝ,H.function w*(Real.cos (q*Real.cosh w):ℂ)

theorem response_continuous (H : RadialTest) : Continuous (response H) := by
  let f := fun q w : ℝ => H.function w*(Real.cos (q*Real.cosh w):ℂ)
  apply continuous_iff_continuousAt.mpr
  intro q
  exact tendsto_integral_filter_of_dominated_convergence (fun w => ‖H.function w‖)
    (Eventually.of_forall fun u => (H.smooth.continuous.mul (by fun_prop)).aestronglyMeasurable)
    (Eventually.of_forall fun u => ae_of_all _ fun w => by
      dsimp only [f]; rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]; simpa using
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (norm_nonneg (H.function w)))
    (H.smooth.continuous.integrable_of_hasCompactSupport H.compact).norm
    (ae_of_all _ fun w => (show Continuous (fun u : ℝ => f u w) by dsimp [f]; fun_prop).continuousAt)

private def env (w : ℝ) := Real.exp (-|w|)

private theorem env_L1 : Integrable env := by
  simpa only [env,neg_one_mul] using abs_exp_integrable (by norm_num : (0:ℝ)<1)

private theorem cos_error (t : ℝ) : |Real.cos t-1|≤2 ∧ |Real.cos t-1|≤t^2/2 := by
  have id : Real.cos t-1= -2*(Real.sin (t/2))^2 := by
    calc
      _ = Real.cos (2*(t/2))-1 := by congr 2; ring
      _ = _ := by rw [Real.cos_two_mul']; nlinarith [Real.sin_sq_add_cos_sq (t/2)]
  refine ⟨(abs_sub _ _).trans (by simpa using add_le_add_right (Real.abs_cos_le_one t) 1),?_⟩
  rw [id,abs_mul,abs_of_nonneg (sq_nonneg _)]
  norm_num
  nlinarith [Real.sin_sq_le_sq (x:=t/2)]

private theorem cosh_exp (w : ℝ) : Real.cosh w ≤ Real.exp |w| := by
  rw [Real.cosh_eq]
  linarith [Real.exp_le_exp.mpr (le_abs_self w),Real.exp_le_exp.mpr (neg_le_abs w)]

/-- At the origin the cost begins quadratically, but after ratio integration
it is linear. The same translated full-line integrable envelope works for
arbitrarily small positive q and arbitrarily large cutoff index. -/
private theorem translated_price {q : ℝ} (hq : 0<q) (w : ℝ) :
    env w*|Real.cos (q*Real.cosh w)-1| ≤ 2*q*env (|w|+Real.log q) := by
  let t := |w|+Real.log q
  have ex : Real.exp t=Real.exp |w|*q := by dsimp [t]; rw [Real.exp_add,Real.exp_log hq]
  have eq : env w=(Real.exp |w|)⁻¹ := Real.exp_neg _
  have qeq := Real.exp_log hq
  rcases le_total 0 t with ht|ht
  · rw [eq,show env (|w|+Real.log q)=(Real.exp t)⁻¹ by rw [env,abs_of_nonneg ht,Real.exp_neg],ex]
    calc
      _ ≤ (Real.exp |w|)⁻¹*2 :=
        mul_le_mul_of_nonneg_left (cos_error _).1 (inv_nonneg.mpr (Real.exp_pos _).le)
      _ = _ := by field_simp [hq.ne',(Real.exp_pos _).ne'] <;> ring
  · rw [eq,show env (|w|+Real.log q)=Real.exp t by simp [env,←show t=|w|+Real.log q from rfl,abs_of_nonpos ht],ex]
    have B := (cos_error (q*Real.cosh w)).2
    have U : (q*Real.cosh w)^2≤(q*Real.exp |w|)^2 :=
      pow_le_pow_left₀ (mul_nonneg hq.le (Real.cosh_pos _).le) (mul_le_mul_of_nonneg_left (cosh_exp w) hq.le) 2
    calc
      _ ≤ (Real.exp |w|)⁻¹*((q*Real.exp |w|)^2/2) :=
        mul_le_mul_of_nonneg_left (B.trans (by linarith)) (inv_nonneg.mpr (Real.exp_pos _).le)
      _ ≤ _ := by
        field_simp [hq.ne',(Real.exp_pos _).ne']
        nlinarith [sq_nonneg (q*Real.exp |w|)]

private theorem translated_integral (t : ℝ) :
    Integrable (fun w : ℝ => env (|w|+t)) ∧
      (∫ w : ℝ,env (|w|+t))≤2*(∫ w : ℝ,env w) := by
  let F := fun w : ℝ => env (w+t)
  have FI : Integrable F := (measurePreserving_add_right volume t).integrable_comp_of_integrable env_L1
  have negI := FI.comp_neg
  let G := fun w : ℝ => env (|w|+t)
  have GI : Integrable G := by
    rw [←integrableOn_univ,←Iic_union_Ioi (a:=(0:ℝ)),integrableOn_union]
    constructor
    · apply negI.integrableOn.congr_fun _ measurableSet_Iic
      intro w hw; simp [G,F,abs_of_nonpos hw]
    · apply FI.integrableOn.congr_fun _ measurableSet_Ioi
      intro w hw; simp [G,F,abs_of_pos hw]
  have split := intervalIntegral.integral_Iic_add_Ioi (b:=(0:ℝ)) GI.integrableOn GI.integrableOn
  have mirror := integral_comp_neg_Ioi (0:ℝ) G
  have E : (∫ w in Ioi (0:ℝ),G w) = ∫ w in Ioi (0:ℝ),F w :=
    setIntegral_congr_fun measurableSet_Ioi (fun w hw => by simp [G,F,abs_of_pos hw])
  have R : (∫ w in Ioi (0:ℝ),G w)≤∫ w : ℝ,env w := by
    rw [E,←integral_add_right_eq_self (f:=env) t]
    exact setIntegral_le_integral FI (ae_of_all _ fun w => (Real.exp_pos _).le)
  simp only [G,abs_neg,neg_zero] at mirror
  refine ⟨GI,?_⟩
  change (∫ w : ℝ,G w)≤_
  rw [←split,←mirror]
  linarith

theorem uniform_response_price (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) :
    ∃ A : ℝ,0≤A ∧ ∀ n (q : ℝ),0<q → ‖response (ratio ell hY n) q‖≤A*q := by
  obtain ⟨K,k,B⟩ := ratio_jets ell hY 0
  simp only [iteratedDeriv_zero] at B
  let M := ∫ w : ℝ,env w
  have m0 : 0≤M := integral_nonneg (fun w => (Real.exp_pos _).le)
  refine ⟨4*K*M,by positivity,fun n q hq => ?_⟩
  let H := (ratio ell hY n).function
  have Hc := (ratio ell hY n).smooth.continuous
  have Hk := (ratio ell hY n).compact
  have Z : response (ratio ell hY n) q=∫ w : ℝ,H w*((Real.cos (q*Real.cosh w):ℂ)-1) := by
    simp_rw [mul_sub,mul_one]
    rw [integral_sub ((Hc.mul (by fun_prop)).integrable_of_hasCompactSupport Hk.mul_right)
      (Hc.integrable_of_hasCompactSupport Hk),ratio_zero ell hY n,sub_zero]; rfl
  obtain ⟨TI,T⟩ := translated_integral (Real.log q)
  rw [Z]
  calc
    _ ≤ ∫ w : ℝ,(K*(2*q))*env (|w|+Real.log q) := by
      apply norm_integral_le_of_norm_le (TI.const_mul _)
      exact ae_of_all _ fun w => by
        rw [norm_mul,←Complex.ofReal_one,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
        calc
          _ ≤ (K*env w)*|Real.cos (q*Real.cosh w)-1| :=
            mul_le_mul_of_nonneg_right (B n w) (abs_nonneg _)
          _ ≤ _ := by rw [mul_assoc,mul_assoc]; exact mul_le_mul_of_nonneg_left (translated_price hq w) k
    _ ≤ _ := by rw [integral_const_mul]; dsimp only [M] at *; nlinarith only [mul_le_mul_of_nonneg_left T (by positivity : 0≤K*(2*q))]

theorem response_limit (ell : D4→ℤ) {Y q : ℝ} (hY : 0<Y) (hq : 0≤q) :
    Tendsto (fun n => response (ratio ell hY n) q) atTop (𝓝 (residual ell Y q)) := by
  rw [original_projection ell hY hq]
  obtain ⟨K,hK,B⟩ := ratio_jets ell hY 0
  simp only [iteratedDeriv_zero] at B
  apply tendsto_integral_of_dominated_convergence (fun w => K*env w)
  · intro n; exact ((ratio ell hY n).smooth.continuous.mul (by fun_prop)).aestronglyMeasurable
  · exact env_L1.const_mul K
  · intro n; exact ae_of_all _ fun w => by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      simpa using mul_le_mul (B n w) (Real.abs_cos_le_one _) (abs_nonneg _) (by positivity)
  · exact ae_of_all _ fun w => (ratio_pointwise ell hY w).mul_const _
end ImbalancedChen.Part3.OriginalPositiveScalarGeometry20261112
end
