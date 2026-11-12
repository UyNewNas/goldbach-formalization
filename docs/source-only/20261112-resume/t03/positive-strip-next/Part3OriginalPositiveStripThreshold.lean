import ImbalancedChen.Part3OriginalPositiveProjection

/-! The zero of the positive numerator is removable in the density multiplier.
Its actual value is the second moment of the same density, including the
weight-two contribution. The formulas with the native spectral denominators
are only divided at nonzero heights. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalPositiveStrip20261112
open Set Filter MeasureTheory Complex
open scoped BigOperators Topology ContDiff
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest)
open ActualPrescribedPositiveJ20261112 (positiveWeight exceptionalWeight weightSchwartz regular_transform)
open OriginalPositiveStripContour20261112 (angular wave norm_wave_real)
open OriginalPositiveStripDensity20261112 (h_jets h_even)
open private abs_exp_integrable from ImbalancedChen.Part3OriginalPositiveStripContour

private def integrand (ell : D4→ℤ) (Y : ℝ) (r : ℕ) (t w : ℝ) : ℂ :=
  h ell Y w*(-2*I*(w:ℂ))^r*wave (2*(t:ℂ)) w

private def jet (ell : D4→ℤ) (Y : ℝ) (r : ℕ) (t : ℝ) := ∫ w : ℝ,integrand ell Y r t w

private theorem modulus (ell : D4→ℤ) (Y : ℝ) (r : ℕ) (t w : ℝ) :
    ‖integrand ell Y r t w‖=‖h ell Y w‖*(2*|w|)^r := by
  simp [integrand,norm_mul,norm_pow,norm_wave_real,Real.norm_eq_abs]

private theorem moment_L1 (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (r : ℕ) :
    Integrable (fun w : ℝ => ‖h ell Y w‖*(2*|w|)^r) := by
  obtain ⟨K,hK,hm⟩ := h_jets ell hY 0
  simp only [iteratedDeriv_zero] at hm
  let A : ℝ := 4^r*(r.factorial:ℝ)
  have A0 : 0≤A := by dsimp only [A]; positivity
  apply ((abs_exp_integrable (by norm_num : (0:ℝ)<1/2)).const_mul (K*A)).mono'
    ((((smooth ell hY).continuous.norm).mul (by fun_prop)).aestronglyMeasurable)
  exact ae_of_all _ fun w => by
    have P := Real.pow_div_factorial_le_exp (show 0≤|w|/2 by positivity) r
    have P' : (2*|w|)^r≤A*Real.exp (|w|/2) := by
      have p := (div_le_iff₀ (by exact_mod_cast r.factorial_pos : 0<(r.factorial:ℝ))).mp P
      rw [show 2*|w|=4*(|w|/2) by ring,mul_pow]
      dsimp only [A]; nlinarith only [mul_le_mul_of_nonneg_left p (by positivity : (0:ℝ)≤4^r)]
    rw [Real.norm_of_nonneg (by positivity : 0≤‖h ell Y w‖*(2*|w|)^r)]
    calc
      _ ≤ (K*Real.exp (-|w|))*(A*Real.exp (|w|/2)) :=
        mul_le_mul (hm w) P' (by positivity) (by positivity)
      _ = _ := by
        rw [show K*Real.exp (-|w|)*(A*Real.exp (|w|/2))=
          (K*A)*(Real.exp (-|w|)*Real.exp (|w|/2)) by ring,←Real.exp_add]
        congr 2; ring

private theorem jet_deriv (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (r : ℕ) (t : ℝ) :
    HasDerivAt (jet ell Y r) (jet ell Y (r+1) t) t := by
  let f := integrand ell Y
  have C (k : ℕ) (u : ℝ) : Continuous (f k u) := by
    dsimp [f,integrand,wave]; fun_prop (disch := exact (smooth ell hY).continuous)
  have i (k : ℕ) (u : ℝ) : Integrable (f k u) :=
    (moment_L1 ell hY k).mono' (C k u).aestronglyMeasurable
      (ae_of_all _ fun w => (modulus ell Y k u w).le)
  have D (w u : ℝ) : HasDerivAt (fun v : ℝ => f r v w) (f (r+1) u w) u := by
    let a := -2*I*(w:ℂ)
    have d := (((hasDerivAt_id (x:=(u:ℂ))).const_mul a).cexp.comp_ofReal).const_mul (h ell Y w*a^r)
    have ex (v : ℝ) : wave (2*(v:ℂ)) w=Complex.exp (a*v) := by
      unfold wave a; congr 1; ring
    convert d using 1
    · funext v; simp only [f,integrand,ex,a]
    · dsimp only [f,integrand]; rw [ex,pow_succ]; dsimp only [a]; ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F:=f r) (F':=f (r+1))
    (bound:=fun w : ℝ => ‖h ell Y w‖*(2*|w|)^(r+1)) (univ_mem : univ∈𝓝 t)
    (Eventually.of_forall fun u => (C r u).aestronglyMeasurable) (i r t)
    (C (r+1) t).aestronglyMeasurable (ae_of_all _ fun w u _ => (modulus ell Y (r+1) u w).le)
    (moment_L1 ell hY (r+1)) (ae_of_all _ fun w u _ => D w u)).2

private theorem jet_zero (ell : D4→ℤ) (Y t : ℝ) : jet ell Y 0 t=hhat ell Y (2*(t:ℂ)) := by
  simp only [jet,integrand,hhat,angular,pow_zero,mul_one]

/-- The first moment vanishes before dividing by either spectral ordinate. -/
theorem first_moment (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) :
    (∫ w : ℝ,(w:ℂ)*h ell Y w)=0 := by
  let f := fun w : ℝ => (w:ℂ)*h ell Y w
  have eq : (fun w : ℝ => f (-w))=fun w => -f w := by
    funext w; simp [f,h_even ell hY]
  have S := MeasureTheory.integral_neg_eq_self (f:=f) (μ:=volume)
  change (∫ w,f (-w))=∫ w,f w at S
  rw [eq,integral_neg] at S
  change ∫ w,f w=0
  linear_combination -S/2

theorem threshold_second_moment (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) :
    positiveWeight (spectralTest ell Y) 0 = -4*(∫ w : ℝ,(w:ℂ)^2*h ell Y w) := by
  let W := weightSchwartz ell hY
  let A := fun t : ℝ => ((Real.cosh (Real.pi*t):ℂ))⁻¹*W t/(2*Real.pi)
  let G := fun t : ℝ => (Real.sinh (Real.pi*t):ℂ)*A t
  have aC : ContDiff ℝ ∞ A := by
    apply ContDiff.div_const
    apply ContDiff.mul _ W.smooth'
    exact (by fun_prop : ContDiff ℝ ∞ (fun t : ℝ => (Real.cosh (Real.pi*t):ℂ))).inv
      fun t => Complex.ofReal_ne_zero.mpr (Real.cosh_pos _).ne'
  have gC : ContDiff ℝ ∞ G :=
    (by fun_prop : ContDiff ℝ ∞ (fun t : ℝ => (Real.sinh (Real.pi*t):ℂ))).mul aC
  have repr : jet ell Y 0=fun t : ℝ => (t:ℂ)*G t := by
    funext t
    rw [jet_zero,regular_multiplier ell hY,(regular_transform ell hY t).2]
    dsimp only [G,A,W]
    rw [show (Real.pi:ℂ)*t=((Real.pi*t:ℝ):ℂ) by push_cast; rfl,←Complex.ofReal_tanh,
      Real.tanh_eq_sinh_div_cosh,Complex.ofReal_div]
    ring
  have gD (u : ℝ) := (gC.differentiable (by simp) u).hasDerivAt
  have D : jet ell Y 1=fun t : ℝ => G t+(t:ℂ)*deriv G t := by
    funext t
    have d := jet_deriv ell hY 0 t
    rw [repr] at d
    simpa only [Complex.ofReal_one,one_mul] using d.unique ((hasDerivAt_id t).ofReal_comp.mul (gD t))
  have g1 : deriv G 0=(W 0)/2 := by
    have s := ((((hasDerivAt_id (0:ℝ)).const_mul Real.pi).sinh).ofReal_comp).mul
      ((aC.differentiable (by simp) 0).hasDerivAt)
    rw [show deriv G 0=_ from s.deriv]
    simp [A,Real.cosh_zero,Real.sinh_zero] <;> field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero] <;> ring
  have d2 := jet_deriv ell hY 1 0
  rw [D] at d2
  have gdd := (((gC.deriv (by simp) : ContDiff ℝ ∞ (deriv G))).differentiable (by simp) 0).hasDerivAt
  have value : jet ell Y 2 0=W 0 := by
    have v := d2.unique ((gD 0).add ((hasDerivAt_id (0:ℝ)).ofReal_comp.mul gdd))
    simpa [g1,add_halves] using v
  rw [(regular_transform ell hY 0).2,←show jet ell Y 2 0=weightSchwartz ell hY 0 from value]
  rw [jet,←integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ fun w => by
    simp [integrand,wave,pow_two,mul_assoc]; ring_nf <;> simp [I_sq] <;> ring

theorem native_regular (ell : D4→ℤ) {Y t : ℝ} (hY : 0<Y) (ht : t≠0) :
    positiveWeight (spectralTest ell Y) t/(Real.cosh (Real.pi*t):ℂ)=
      (2*Real.pi:ℂ)*hhat ell Y (2*(t:ℂ))/((t:ℂ)*(Real.sinh (Real.pi*t):ℂ)) := by
  have hn : Real.sinh (Real.pi*t)≠0 := Real.sinh_ne_zero.mpr (mul_ne_zero Real.pi_ne_zero ht)
  rw [regular_multiplier ell hY,show (Real.pi:ℂ)*t=((Real.pi*t:ℝ):ℂ) by push_cast; rfl,
    ←Complex.ofReal_tanh,Real.tanh_eq_sinh_div_cosh,Complex.ofReal_div]
  field_simp [Complex.ofReal_ne_zero.mpr ht,Complex.ofReal_ne_zero.mpr hn,
    Complex.ofReal_ne_zero.mpr (Real.cosh_pos _).ne',Complex.ofReal_ne_zero.mpr Real.pi_ne_zero] <;> ring

theorem native_complementary (ell : D4→ℤ) {Y a : ℝ} (hY : 0<Y) (ha : 0<a) (ha1 : a<1/2) :
    exceptionalWeight (spectralTest ell Y) a/(Real.cos (Real.pi*a):ℂ)=
      -(2*Real.pi:ℂ)*hhat ell Y (2*(a:ℂ)*I)/((a:ℂ)*(Real.sin (Real.pi*a):ℂ)) := by
  have pa := mul_pos Real.pi_pos ha
  have pp : Real.pi*a<Real.pi/2 := by nlinarith [mul_lt_mul_of_pos_left ha1 Real.pi_pos]
  have cs := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],pp⟩
  have sn := Real.sin_pos_of_pos_of_lt_pi pa (by linarith [Real.pi_pos])
  rw [complementary_multiplier ell hY ha.le ha1,Real.tan_eq_sin_div_cos,Complex.ofReal_div]
  field_simp [Complex.ofReal_ne_zero.mpr ha.ne',Complex.ofReal_ne_zero.mpr cs.ne',
    Complex.ofReal_ne_zero.mpr sn.ne',Complex.ofReal_ne_zero.mpr Real.pi_ne_zero] <;> ring
end ImbalancedChen.Part3.OriginalPositiveStrip20261112
end
