import ImbalancedChen.Part3OriginalRegularPreKuznetsovInduced

/-! Gaussian averaging of the actual induced Bruhat test at s=1.
Absolute convergence of the r,ξ integral precedes the Fourier identity. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalRegularPreKuznetsovAverage20261113
open Set MeasureTheory Complex
open OriginalRegularPreKuznetsovGaussian20261113 (weight weight_nonnegative)
open OriginalRegularPreKuznetsovFourier20261113 (character fourier_gaussian_weight)
open OriginalRegularPreKuznetsovAngle20261113 (angular angularWave angular_derivative)
open OriginalRegularPreKuznetsovOrbitL120261113 (polarWave polar_integrable angleMeasure)
open OriginalRegularPreKuznetsovPolar20261113 (physical)
open OriginalRegularPreKuznetsovInduced20261113 (induced_boundary)
open OriginalPositiveScalarGeometry20261112 (induced)

def G (K ξ : ℝ) := Real.exp (-(K*ξ)^2)
def P (K ξ : ℝ) := (1-2*(K*ξ)^2)*G K ξ

theorem gaussian_integrable {K : ℝ} (hK : 0<K) : Integrable (G K) := by
  simpa only [G,mul_pow,neg_mul] using integrable_exp_neg_mul_sq (sq_pos_of_pos hK)

theorem gaussian_first_integrable {K : ℝ} (hK : 0<K) :
    Integrable (fun ξ : ℝ => ξ*G K ξ) := by
  simpa only [G,mul_pow,neg_mul] using integrable_mul_exp_neg_mul_sq (sq_pos_of_pos hK)

theorem gaussian_second_integrable {K : ℝ} (hK : 0<K) :
    Integrable (fun ξ : ℝ => ξ^2*G K ξ) := by
  simpa only [G,mul_pow,neg_mul,Real.rpow_two] using
    (integrable_rpow_mul_exp_neg_mul_sq (sq_pos_of_pos hK) (by norm_num : (-1:ℝ)<(2:ℝ)))

theorem polynomial_integrable {K : ℝ} (hK : 0<K) : Integrable (P K) := by
  have p := (gaussian_integrable hK).sub ((gaussian_second_integrable hK).const_mul (2*K^2))
  apply p.congr
  filter_upwards with ξ
  dsimp only [P];ring

theorem weight_integrable {K : ℝ} (hK : 0<K) : Integrable (weight K) := by
  apply (gaussian_second_integrable (inv_pos.mpr hK)).congr
  filter_upwards with r
  dsimp only [G,weight]
  rw [div_eq_inv_mul]

theorem angular_line_integrable {u : ℝ} (hu : 0<u) :
    Integrable (fun ξ : ℝ => angular (u*Real.cosh ξ)) := by
  have h := (polar_integrable (show 0≤(0:ℝ) by norm_num) hu 0).integral_prod_left
  apply h.congr
  filter_upwards with ξ
  simp only [Function.uncurry,polarWave,character,Complex.ofReal_zero,mul_zero,zero_mul,
    Real.rpow_zero,Complex.ofReal_one,Complex.exp_zero,one_mul]
  rw [angular,intervalIntegral.integral_of_le Real.pi_pos.le,integral_Ioc_eq_integral_Ioo] <;> rfl

def gaussianOrbit (K u : ℝ) : ℂ :=
  ∫ r : ℝ,(weight K r:ℂ)*induced (fun a b => physical 0 r a*star (physical 0 r b)) u

/-- The raw full-line r² Gaussian average of the native coefficient has
the exact coefficient πu√πK³/8 in front of the zero-mass polynomial. -/
theorem averaged_orbit {K u : ℝ} (hK : 0<K) (hu : 0<u) :
    gaussianOrbit K u=((Real.pi*u*Real.sqrt Real.pi*K^3/8:ℝ):ℂ)*
      (∫ ξ : ℝ,(P K ξ:ℂ)*angular (u*Real.cosh ξ)) := by
  let a := fun ξ : ℝ => angular (u*Real.cosh ξ)
  let F := fun z : ℝ×ℝ => (weight K z.1:ℂ)*character z.2 z.1*a z.2
  have ac : Continuous a := by
    rw [continuous_iff_continuousAt]
    intro ξ
    exact (angular_derivative (mul_pos hu (Real.cosh_pos ξ))).continuousAt.comp
      (show ContinuousAt (fun v : ℝ => u*Real.cosh v) ξ by fun_prop)
  have Fint : Integrable F ((volume:Measure ℝ).prod volume) := by
    have major := (weight_integrable hK).mul_prod (angular_line_integrable hu).norm
    apply major.mono' (show Continuous F by dsimp only [F,weight,character];fun_prop).aestronglyMeasurable
    filter_upwards with z
    have ch : ‖character z.2 z.1‖=1 := by simp [character,Complex.norm_exp,Complex.mul_re,Complex.mul_im]
    simp only [F,norm_mul,Complex.norm_real,Real.norm_of_nonneg (weight_nonnegative K z.1),ch,mul_one,a,le_refl]
  let C : ℂ := (Real.pi*u/4:ℝ)
  have row (r : ℝ) :
      (weight K r:ℂ)*induced (fun a b => physical 0 r a*star (physical 0 r b)) u=C*∫ ξ : ℝ,F (r,ξ) := by
    rw [induced_boundary hu]
    simp only [F,mul_assoc,integral_const_mul,C,a]
    ring
  rw [gaussianOrbit]
  simp_rw [row,integral_const_mul]
  rw [integral_integral_swap Fint]
  have col (ξ : ℝ) : (∫ r : ℝ,F (r,ξ))=((Real.sqrt Real.pi*K^3/2:ℝ):ℂ)*((P K ξ:ℂ)*a ξ) := by
    simp only [F,integral_mul_const,fourier_gaussian_weight hK,P,G,Complex.ofReal_mul]
    ring
  simp_rw [col,integral_const_mul]
  dsimp only [C,a]
  push_cast
  ring

end ImbalancedChen.Part3.OriginalRegularPreKuznetsovAverage20261113
end
