import ImbalancedChen.Part3OriginalRegularPreKuznetsovOscillation
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-! A fixed integrable even Gaussian in v=Kξ pays both native orbital
weights. The extra v² on the large-angle set pays the second power of K. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalRegularGaussianMoment20261113
open Real Set MeasureTheory
open OriginalRegularPreKuznetsovAverage20261113 (G)

def major (v : ℝ) := 4*(1+v^2)^2*exp (-(v^2)/2)
def bill := ∫ v : ℝ,major v

theorem major_nonnegative (v : ℝ) : 0≤major v := by unfold major; positivity

theorem major_integrable : Integrable major := by
  let H := fun v : ℝ => exp (-(1/2)*v^2)
  have g : Integrable H := integrable_exp_neg_mul_sq (by norm_num : 0<(1/2:ℝ))
  have g2 : Integrable (fun v : ℝ => v^2*H v) := by
    simpa only [H,Real.rpow_two] using
      (integrable_rpow_mul_exp_neg_mul_sq (b:=(1/2:ℝ)) (by norm_num) (s:=(2:ℝ)) (by norm_num))
  have g4 : Integrable (fun v : ℝ => v^4*H v) := by
    have h : Integrable (fun v : ℝ => v^((4:ℕ):ℝ)*H v) :=
      integrable_rpow_mul_exp_neg_mul_sq (b:=(1/2:ℝ)) (by norm_num) (by norm_num)
    simpa only [Real.rpow_natCast] using h
  apply (((g.add (g2.const_mul 2)).add g4).const_mul 4).congr
  filter_upwards with v
  dsimp only [H,major]
  rw [show -(1/2:ℝ)*v^2= -(v^2)/2 by ring]
  ring

theorem bill_nonnegative : 0≤bill := integral_nonneg major_nonnegative

theorem major_scale {K : ℝ} (hK : 0<K) :
    Integrable (fun ξ : ℝ => major (K*ξ)) ∧ (∫ ξ : ℝ,major (K*ξ))=K⁻¹*bill := by
  refine ⟨(integrable_comp_mul_left_iff major hK.ne').mpr major_integrable,?_⟩
  have h := Measure.integral_comp_mul_left major K
  simpa only [bill,smul_eq_mul,abs_inv,abs_of_pos hK] using h

private theorem tanh_abs (ξ : ℝ) : |tanh ξ|≤|ξ| := by
  have h : ∀ x : ℝ,0≤x → sinh x≤x*cosh x := by
    let f := fun x : ℝ => x*cosh x-sinh x
    have d (x : ℝ) : HasDerivAt f (x*sinh x) x := by
      convert ((hasDerivAt_id x).mul (hasDerivAt_cosh x)).sub (hasDerivAt_sinh x) using 1 <;> dsimp only [f,id_eq] <;> ring
    have m : MonotoneOn f (Ici (0:ℝ)) :=
      monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici _) (by dsimp only [f];fun_prop)
        (fun x _ => (d x).hasDerivWithinAt)
        (fun x hx => mul_nonneg (interior_subset hx) (sinh_nonneg_iff.mpr (interior_subset hx)))
    intro x hx
    have v := m (self_mem_Ici (a:=(0:ℝ))) hx hx
    simpa [f] using v
  rw [tanh_eq_sinh_div_cosh,abs_div,abs_of_pos (cosh_pos _),div_le_iff₀ (cosh_pos _),
    Real.abs_sinh]
  simpa only [cosh_abs] using h |ξ| (abs_nonneg _)

theorem cosh_near {ξ : ℝ} (near : |ξ|≤1) : cosh ξ≤2 := by
  have h : cosh ξ≤cosh 1 := Real.cosh_le_cosh.mpr (by simpa only [abs_one] using near)
  rw [cosh_eq (1:ℝ)] at h
  have m := exp_le_one_iff.mpr (by norm_num : -(1:ℝ)≤0)
  linarith only [h,m,Real.exp_one_lt_d9]

private theorem exponential_bound {K : ℝ} (hK : 2≤K) (ξ : ℝ) :
    G K ξ*cosh ξ^2≤exp (-((K*ξ)^2)/2) := by
  have c := pow_le_pow_left₀ (cosh_pos ξ).le (Real.cosh_le_exp_half_sq ξ) 2
  have h := mul_le_mul_of_nonneg_left c (Real.exp_pos (-((K*ξ)^2))).le
  rw [G]
  apply h.trans
  rw [show (exp (ξ^2/2))^2=exp (ξ^2/2+ξ^2/2) by rw [sq,←exp_add],←exp_add,Real.exp_le_exp]
  have k2 : 2≤K^2 := by nlinarith only [hK,sq_nonneg (K-2)]
  have q := mul_le_mul_of_nonneg_right k2 (sq_nonneg ξ)
  nlinarith only [q]

def sineWeight (K ξ : ℝ) := |ξ*tanh ξ|*G K ξ
def cosineWeight (K ξ : ℝ) := |1-ξ*tanh ξ-2*(K*ξ)^2|*G K ξ/cosh ξ

private theorem polynomial (K ξ : ℝ) (hK : 2≤K) :
    |1-ξ*tanh ξ-2*(K*ξ)^2|≤1+3*(K*ξ)^2 := by
  have a := abs_sub (1-ξ*tanh ξ) (2*(K*ξ)^2)
  have b := abs_sub 1 (ξ*tanh ξ)
  rw [abs_one] at b
  rw [abs_of_nonneg (by positivity : 0≤2*(K*ξ)^2)] at a
  have t := mul_le_mul_of_nonneg_left (tanh_abs ξ) (abs_nonneg ξ)
  rw [←abs_mul,←sq,sq_abs] at t
  have k1 : 1≤K^2 := by nlinarith only [hK,sq_nonneg (K-1)]
  have e := mul_le_mul_of_nonneg_right k1 (sq_nonneg ξ)
  nlinarith only [a,b,t,e]

theorem sine_major {K : ℝ} (hK : 2≤K) (ξ : ℝ) :
    K^2*sineWeight K ξ*cosh ξ^2≤major (K*ξ) := by
  have t := mul_le_mul_of_nonneg_left (tanh_abs ξ) (abs_nonneg ξ)
  rw [←abs_mul,←sq,sq_abs] at t
  have g0 : 0≤G K ξ := (Real.exp_pos _).le
  have p := mul_le_mul_of_nonneg_left t (sq_nonneg K)
  have w := mul_le_mul p (exponential_bound hK ξ) (mul_nonneg g0 (sq_nonneg _))
    (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have P := sq_nonneg ((K*ξ)^2)
  have d : (K*ξ)^2≤4*(1+(K*ξ)^2)^2 := by nlinarith only [P,sq_nonneg (K*ξ)]
  have s := mul_le_mul_of_nonneg_right d (exp_pos (-((K*ξ)^2)/2)).le
  dsimp only [major,sineWeight]
  nlinarith only [w,s]

/-- Off the central hyperbolic interval, the sine representation pays the
full weak oscillatory form and the factor M/c up to K². -/
theorem sine_far_major {K : ℝ} (hK : 2≤K) {ξ : ℝ} (far : 1≤|ξ|) :
    K^4*sineWeight K ξ*cosh ξ≤major (K*ξ) := by
  have t := mul_le_mul_of_nonneg_left (tanh_abs ξ) (abs_nonneg ξ)
  rw [←abs_mul,←sq,sq_abs] at t
  have e := pow_le_pow_left₀ (by norm_num : 0≤(1:ℝ)) far 2
  rw [one_pow,sq_abs] at e
  have p := mul_le_mul_of_nonneg_left t (sq_nonneg K)
  have v := mul_le_mul_of_nonneg_left e (sq_nonneg K)
  have u := mul_le_mul v p (mul_nonneg (sq_nonneg _) (abs_nonneg _))
    (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have g0 : 0≤G K ξ := (exp_pos _).le
  have w := mul_le_mul_of_nonneg_left
    (show cosh ξ≤cosh ξ^2 by nlinarith only [one_le_cosh ξ,sq_nonneg (cosh ξ-1)]) g0
  have b := mul_le_mul u (w.trans (exponential_bound hK ξ))
    (mul_nonneg g0 (cosh_pos _).le) (by positivity)
  have d : (K^2*ξ^2)*(K^2*ξ^2) ≤ 4*(1+(K*ξ)^2)^2 := by
    nlinarith only [sq_nonneg ((K*ξ)^2),sq_nonneg (K*ξ)]
  have s := mul_le_mul_of_nonneg_right d (exp_pos (-((K*ξ)^2)/2)).le
  dsimp only [major,sineWeight]
  nlinarith only [b,s]

theorem cosine_major {K : ℝ} (hK : 2≤K) (ξ : ℝ) :
    cosineWeight K ξ≤major (K*ξ) := by
  have C := one_le_cosh ξ
  have c := cosh_pos ξ
  have G0 : 0≤G K ξ := (exp_pos _).le
  have expbd : G K ξ≤exp (-((K*ξ)^2)/2) := by
    rw [G,Real.exp_le_exp];nlinarith only [sq_nonneg (K*ξ)]
  have w := mul_le_mul (polynomial K ξ hK) expbd G0 (by positivity)
  have h : 1+3*(K*ξ)^2≤4*(1+(K*ξ)^2)^2 := by
    nlinarith only [sq_nonneg (K*ξ),sq_nonneg ((K*ξ)^2)]
  have a := mul_le_mul_of_nonneg_right h (exp_pos (-((K*ξ)^2)/2)).le
  apply (div_le_self (mul_nonneg (abs_nonneg _) G0) C).trans
  dsimp only [major]
  nlinarith only [w,a]

/-- Large |ξ| retains two additional inverse powers of K, even after
the unrestricted-parameter form contributes one complete cosh ξ. -/
theorem cosine_far_major {K : ℝ} (hK : 2≤K) {ξ : ℝ} (far : 1≤|ξ|) :
    K^2*cosineWeight K ξ*cosh ξ≤major (K*ξ) := by
  have g0 : 0≤G K ξ := (exp_pos _).le
  have expbd : G K ξ≤exp (-((K*ξ)^2)/2) := by
    rw [G,Real.exp_le_exp];nlinarith only [sq_nonneg (K*ξ)]
  have k2 : K^2≤(K*ξ)^2 := by
    have d := pow_le_pow_left₀ (by norm_num : 0≤(1:ℝ)) far 2
    rw [one_pow,sq_abs] at d
    have w := mul_le_mul_of_nonneg_left d (sq_nonneg K)
    nlinarith only [w]
  have h := mul_le_mul k2 (polynomial K ξ hK) (abs_nonneg _) (sq_nonneg _)
  have b : (K*ξ)^2*(1+3*(K*ξ)^2)≤4*(1+(K*ξ)^2)^2 := by
    nlinarith only [sq_nonneg (K*ξ),sq_nonneg ((K*ξ)^2)]
  have d := mul_le_mul (h.trans b) expbd g0 (by positivity)
  dsimp only [cosineWeight,major]
  convert d using 1 <;> field_simp [(cosh_pos ξ).ne'] <;> ring

theorem integral_price {K B : ℝ} (hK : 2≤K) (F : ℝ→ℂ) (hF : Integrable F)
    (bound : ∀ ξ,K^2*‖F ξ‖≤B*major (K*ξ)) :
    K^3*‖∫ ξ : ℝ,F ξ‖≤B*bill := by
  have kp : 0<K := by linarith only [hK]
  have h := integral_mono (hF.norm.const_mul (K^2)) ((major_scale kp).1.const_mul B) bound
  simp only [integral_const_mul,(major_scale kp).2] at h
  have d := mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm F) (sq_nonneg K)
  have e := mul_le_mul_of_nonneg_left (d.trans h) kp.le
  convert e using 1 <;> field_simp [kp.ne'] <;> ring

end ImbalancedChen.Part3.OriginalRegularGaussianMoment20261113
end
