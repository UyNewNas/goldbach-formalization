import ImbalancedChen.Part3OriginalRegularPreKuznetsovAverage

/-! The two complementary positive-modulus formulas for the actual
Gaussian pre-Kuznetsov test. All full-line integrations by parts have
integrable primitives and derivatives. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalRegularPreKuznetsovOscillation20261113
open Complex MeasureTheory
open OriginalRegularPreKuznetsovAverage20261113
open OriginalRegularPreKuznetsovAngle20261113 (angular angular_derivative angular_norm)

def sinFactor (u ξ : ℝ) : ℝ := Real.tanh ξ*Real.sin (u*Real.cosh ξ)
def sinDensity (K u ξ : ℝ) : ℝ := ξ*G K ξ*sinFactor u ξ
def cosFactor (u ξ : ℝ) := Real.cos (u*Real.cosh ξ)/Real.cosh ξ
def cosCorrection (u ξ : ℝ) := Real.tanh ξ*cosFactor u ξ
def cosDensity (K u ξ : ℝ) : ℝ :=
  (1-ξ*Real.tanh ξ-2*(K*ξ)^2)*G K ξ*cosFactor u ξ

private theorem phaseBound (u ξ : ℝ) : |sinFactor u ξ|≤1 := by
  rw [sinFactor,abs_mul]
  exact mul_le_one₀ (Real.abs_tanh_lt_one _).le (abs_nonneg _) (Real.abs_sin_le_one _)

private theorem cosBound (u ξ : ℝ) : |cosFactor u ξ|≤1 := by
  rw [cosFactor,abs_div,abs_of_pos (Real.cosh_pos _),div_le_one (Real.cosh_pos _)]
  exact (Real.abs_cos_le_one _).trans (Real.one_le_cosh _)

private theorem correctionBound (u ξ : ℝ) : |cosCorrection u ξ|≤1 := by
  rw [cosCorrection,abs_mul]
  exact mul_le_one₀ (Real.abs_tanh_lt_one _).le (abs_nonneg _) (cosBound _ _)

private theorem mul_bound {w f : ℝ→ℝ} (wi : Integrable w) (cf : Continuous f)
    (h : ∀ ξ,|f ξ|≤1) : Integrable (fun ξ => w ξ*f ξ) := by
  apply wi.norm.mono' (wi.aestronglyMeasurable.mul cf.aestronglyMeasurable)
  filter_upwards with ξ
  simp only [norm_mul,Real.norm_eq_abs]
  exact mul_le_of_le_one_right (abs_nonneg _) (h ξ)

private theorem mul_angle {w : ℝ→ℝ} (wi : Integrable w) {u : ℝ} (hu : 0<u) :
    Integrable (fun ξ => (w ξ:ℂ)*angular (u*Real.cosh ξ)) := by
  have cont : Continuous (fun ξ => angular (u*Real.cosh ξ)) := by
    rw [continuous_iff_continuousAt]
    intro ξ
    exact (angular_derivative (mul_pos hu (Real.cosh_pos ξ))).continuousAt.comp
      (show ContinuousAt (fun v : ℝ => u*Real.cosh v) ξ by fun_prop)
  apply (wi.norm.const_mul Real.pi).mono'
    ((Complex.continuous_ofReal.comp_aestronglyMeasurable wi.aestronglyMeasurable).mul cont.aestronglyMeasurable)
  filter_upwards with ξ
  rw [norm_mul,Complex.norm_real,mul_comm Real.pi]
  exact mul_le_mul_of_nonneg_left (angular_norm (mul_pos hu (Real.cosh_pos ξ)).le) (norm_nonneg _)

private theorem hdiff (K ξ : ℝ) : HasDerivAt (fun v => v*G K v) (P K ξ) ξ := by
  convert (hasDerivAt_id ξ).mul (((((hasDerivAt_id ξ).const_mul K).pow 2).neg).exp) using 1 <;>
    dsimp only [G,P,id_eq] <;> ring

private theorem adiff {u : ℝ} (hu : 0<u) (ξ : ℝ) :
    HasDerivAt (fun v : ℝ => angular (u*Real.cosh v)) ((-2*sinFactor u ξ:ℝ):ℂ) ξ := by
  have d := (angular_derivative (mul_pos hu (Real.cosh_pos ξ))).scomp ξ ((Real.hasDerivAt_cosh ξ).const_mul u)
  convert d using 1 <;> simp only [sinFactor,Real.tanh_eq_sinh_div_cosh,Complex.real_smul,
    Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_neg,Complex.ofReal_ofNat] <;>
    field_simp [Complex.ofReal_ne_zero.mpr hu.ne',Complex.ofReal_ne_zero.mpr (Real.cosh_pos ξ).ne'] <;> ring

private theorem cosdiff (u ξ : ℝ) :
    HasDerivAt (cosFactor u) (-u*sinFactor u ξ-cosCorrection u ξ) ξ := by
  have d := ((Real.hasDerivAt_cos (u*Real.cosh ξ)).comp ξ ((Real.hasDerivAt_cosh ξ).const_mul u)).div
    (Real.hasDerivAt_cosh ξ) (Real.cosh_pos ξ).ne'
  convert d using 1 <;> dsimp only [cosFactor,sinFactor,cosCorrection,Real.tanh_eq_sinh_div_cosh] <;>
    field_simp [(Real.cosh_pos ξ).ne'] <;> ring

private theorem sinI {K : ℝ} (hK : 0<K) (u : ℝ) : Integrable (sinDensity K u) :=
  mul_bound (gaussian_first_integrable hK) (by unfold sinFactor;fun_prop) (phaseBound u)

private theorem cosI {K : ℝ} (hK : 0<K) (u : ℝ) : Integrable (cosDensity K u) := by
  have a := mul_bound (polynomial_integrable hK) (by unfold cosFactor;fun_prop (disch := exact (Real.cosh_pos _).ne')) (cosBound u)
  have b := mul_bound (gaussian_first_integrable hK)
    (by unfold cosCorrection cosFactor;fun_prop (disch := exact (Real.cosh_pos _).ne')) (correctionBound u)
  apply (a.sub b).congr
  filter_upwards with ξ
  dsimp only [P,cosDensity,cosCorrection];ring

private theorem ibp_sin {K u : ℝ} (hK : 0<K) (hu : 0<u) :
    (∫ ξ : ℝ,(P K ξ:ℂ)*angular (u*Real.cosh ξ))=2*∫ ξ : ℝ,(sinDensity K u ξ:ℂ) := by
  let f := fun ξ : ℝ => ((ξ*G K ξ:ℝ):ℂ)*angular (u*Real.cosh ξ)
  let p := fun ξ : ℝ => (P K ξ:ℂ)*angular (u*Real.cosh ξ)
  let s := fun ξ : ℝ => (sinDensity K u ξ:ℂ)
  have pi : Integrable p := mul_angle (polynomial_integrable hK) hu
  have si : Integrable s := Complex.ofRealCLM.integrable_comp (sinI hK u)
  have d (ξ : ℝ) : HasDerivAt f (p ξ-2*s ξ) ξ := by
    convert (hdiff K ξ).ofReal_comp.mul (adiff hu ξ) using 1 <;>
      dsimp only [p,s,sinDensity] <;> push_cast <;> ring
  have id := integral_eq_zero_of_hasDerivAt_of_integrable d (pi.sub (si.const_mul 2))
    (mul_angle (gaussian_first_integrable hK) hu)
  rw [integral_sub pi (si.const_mul 2),integral_const_mul,sub_eq_zero] at id
  exact id

private theorem ibp_cos {K : ℝ} (hK : 0<K) (u : ℝ) :
    u*(∫ ξ : ℝ,sinDensity K u ξ)=∫ ξ : ℝ,cosDensity K u ξ := by
  let f := fun ξ : ℝ => ξ*G K ξ*cosFactor u ξ
  have fi : Integrable f := mul_bound (gaussian_first_integrable hK)
    (by unfold cosFactor;fun_prop (disch := exact (Real.cosh_pos _).ne')) (cosBound u)
  have d (ξ : ℝ) : HasDerivAt f (cosDensity K u ξ-u*sinDensity K u ξ) ξ := by
    convert (hdiff K ξ).mul (cosdiff u ξ) using 1 <;>
      dsimp only [P,cosDensity,sinDensity,cosCorrection] <;> ring
  have id := integral_eq_zero_of_hasDerivAt_of_integrable d
    ((cosI hK u).sub ((sinI hK u).const_mul u)) fi
  rw [integral_sub (cosI hK u) ((sinI hK u).const_mul u),integral_const_mul,sub_eq_zero] at id
  exact id.symm

theorem sine_orbit {K u : ℝ} (hK : 0<K) (hu : 0<u) :
    gaussianOrbit K u=((Real.pi*Real.sqrt Real.pi*K^3/4*u:ℝ):ℂ)*
      (∫ ξ : ℝ,sinDensity K u ξ:ℝ) := by
  rw [averaged_orbit hK hu,ibp_sin hK hu,integral_complex_ofReal]
  push_cast;ring

theorem cosine_orbit {K u : ℝ} (hK : 0<K) (hu : 0<u) :
    gaussianOrbit K u=((Real.pi*Real.sqrt Real.pi*K^3/4:ℝ):ℂ)*
      (∫ ξ : ℝ,cosDensity K u ξ:ℝ) := by
  rw [sine_orbit hK hu,←ibp_cos hK u]
  push_cast;ring

end ImbalancedChen.Part3.OriginalRegularPreKuznetsovOscillation20261113
end
