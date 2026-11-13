import ImbalancedChen.Part3OriginalRegularGaussianSingleModulus
import ImbalancedChen.Part3OriginalHolomorphicLongModulus

/-! The sine vanishing at the origin gives another complete reciprocal
modulus before the absolute sum of the true Gaussian coefficients. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalRegularGaussianLongModulus20261113
open Real Set MeasureTheory Finset
open OriginalHolomorphicPhysicalCosine20261113 (form argument scale cosineForm)
open OriginalHolomorphicShortOscillation20261113 (sineForm rowProduct rootRow root_row_product row_product_nonnegative)
open OriginalRegularGaussianForms20261113
open OriginalRegularGaussianMoment20261113
open OriginalRegularGaussianSingleModulus20261113
open private form_integral from ImbalancedChen.Part3OriginalHolomorphicLongModulus

def longConstant := normalization*bill*(48*exp (4*π)*(4*π)^2)

private theorem sin_first (u : ℝ) : sin u=u*(∫ s in (0:ℝ)..1,cos (s*u)) := by
  have d (s : ℝ) : HasDerivAt (fun x : ℝ => sin (x*u)) (u*cos (s*u)) s := by
    convert ((hasDerivAt_id s).mul_const u).sin using 1 <;> dsimp <;> ring
  rw [←intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => d s)
      ((show Continuous (fun s : ℝ => u*cos (s*u)) by fun_prop).intervalIntegrable 0 1)]
  simp only [one_mul,zero_mul,sin_zero,sub_zero]

private theorem sine_integral (M c : ℕ) (q : ℝ) (a b : ℕ→ℂ) :
    sineForm M c q a b=((q*scale c:ℝ):ℂ)*
      ∫ s in (0:ℝ)..1,cosineForm M c (s*q) (rootRow a) (rootRow b) := by
  have coef (m n : ℕ) : (sin (q*argument c m n):ℂ)=
      ∫ s in (0:ℝ)..1, ((q*argument c m n:ℝ):ℂ)*(cos ((s*q)*argument c m n):ℂ) := by
    rw [sin_first,Complex.ofReal_mul,←intervalIntegral.integral_ofReal,intervalIntegral.integral_const_mul]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    rw [mul_assoc]
  dsimp only [sineForm]
  simp_rw [coef]
  rw [form_integral M c a b _ (by intro m n;fun_prop),←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only [cosineForm,form,argument,rootRow]
  simp only [mul_sum]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  push_cast
  ring

private theorem root_twice (M : ℕ) (a b : ℕ→ℂ) :
    rowProduct M (rootRow (rootRow a)) (rootRow (rootRow b))≤4*(M:ℝ)^2*rowProduct M a b := by
  have A := root_row_product M (rootRow a) (rootRow b)
  have B := mul_le_mul_of_nonneg_left (root_row_product M a b) (show 0≤2*(M:ℝ) by positivity)
  nlinarith only [A,B]

private theorem long_integral {M c : ℕ} [NeZero c] (hM : 0<M) (hc : M≤c)
    (ξ : ℝ) (a b : ℕ→ℂ) :
    ‖∫ s in (0:ℝ)..1,cosineForm M c (s*cosh ξ) (rootRow (rootRow a)) (rootRow (rootRow b))‖≤
      48*exp (4*π)*c*cosh ξ*M^2*rowProduct M a b := by
  let A := rootRow (rootRow a)
  let B := rootRow (rootRow b)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a:=(0:ℝ)) (b:=1)
    (f:=fun s : ℝ => cosineForm M c (s*cosh ξ) A B)
    (C:=48*exp (4*π)*c*cosh ξ*M^2*rowProduct M a b) (fun s hs => by
      rw [uIoc_of_le (by norm_num : (0:ℝ)≤1)] at hs
      have hθ := cosh_pos ξ
      have q1 := mul_le_mul_of_nonneg_right hs.2 hθ.le
      rw [one_mul] at q1
      have q0 := mul_nonneg hs.1.le hθ.le
      have cost := uniform_cost (M:=M) (c:=c) (D:=(c:ℝ)) (by exact_mod_cast hc)
        (le_refl _) (one_le_cosh ξ) q1
      have u := (all_forms hM q0 A B).1
      have v := mul_le_mul cost (root_twice M a b) (row_product_nonnegative M A B)
        (show 0≤3*(c:ℝ)*cosh ξ by positivity)
      have w := mul_le_mul_of_nonneg_left v (show 0≤4*exp (4*π) by positivity)
      dsimp only [A,B] at *
      nlinarith only [u,w])
  simpa only [sub_zero,abs_one,mul_one,A,B] using h

private theorem long_kernel {M c : ℕ} [NeZero c] (hM : 0<M) (hc : M≤c)
    {K : ℝ} (hK : 2≤K) (a b : ℕ→ℂ) (ξ : ℝ) :
    K^2*‖sinKernel M c K a b ξ‖≤
      (48*exp (4*π)*(4*π)^2*((M:ℝ)^2/c)*rowProduct M a b)*major (K*ξ) := by
  have cp : 0<(c:ℝ) := by exact_mod_cast NeZero.pos c
  have sc : 0≤scale c := by dsimp only [scale];positivity
  have hθ := cosh_pos ξ
  have e0 := row_product_nonnegative M a b
  have h := long_integral hM hc ξ a b
  rw [norm_sinKernel,sine_integral,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hθ.le sc)]
  have v := mul_le_mul_of_nonneg_left h
    (show 0≤K^2*(scale c*sineWeight K ξ)*(cosh ξ*scale c) by
      have a0 := sine_nonnegative K ξ;positivity)
  have w := mul_le_mul_of_nonneg_right (sine_major hK ξ)
    (show 0≤(scale c)^2*48*exp (4*π)*c*M^2*rowProduct M a b by positivity)
  have scalar : (scale c)^2*(c:ℝ)=(4*π)^2/c := by
    dsimp only [scale];field_simp [cp.ne'] <;> ring
  calc
    _ ≤ (K^2*sineWeight K ξ*cosh ξ^2)*((scale c)^2*48*exp (4*π)*c*M^2*rowProduct M a b) := by
      nlinarith only [v]
    _ ≤ _ := by
      apply w.trans_eq
      calc
        _=major (K*ξ)*(48*exp (4*π)*((scale c)^2*c)*M^2*rowProduct M a b) := by ring
        _=_ := by rw [scalar];ring

theorem long_modulus {M c : ℕ} [NeZero c] (hM : 0<M) (hc : M≤c)
    {K : ℝ} (hK : 2≤K) (a b : ℕ→ℂ) :
    ‖numerator M c K a b‖≤longConstant*((M:ℝ)^2/c)*rowProduct M a b := by
  have kp : 0<K := by linarith only [hK]
  obtain ⟨si,_,S,_⟩ := numerator_forms hM kp a b
  rw [S,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg normalization_pos.le (pow_nonneg kp.le 3))]
  have w := mul_le_mul_of_nonneg_left
    (integral_price hK _ si (long_kernel hM hc hK a b)) normalization_pos.le
  dsimp only [longConstant]
  simp only [div_eq_mul_inv] at w ⊢
  nlinarith only [w]

end ImbalancedChen.Part3.OriginalRegularGaussianLongModulus20261113
end

