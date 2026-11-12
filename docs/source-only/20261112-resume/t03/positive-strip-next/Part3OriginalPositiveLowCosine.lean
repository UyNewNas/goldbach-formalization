import ImbalancedChen.Part3OriginalPositiveStripDensity
import ImbalancedChen.Part3OriginalPositiveQuarterContour

/-! The low interval 0 ≤ s ≤ 1 is precisely the odd J part of the original
cosine transform when s = sin θ, with its true Jacobian cos θ. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalPositiveLowCosine20261112
open Set Filter MeasureTheory Complex
open scoped BigOperators Topology ContDiff
open P3NativePeriod64SamplingSourceOnly (D4)
open ActualPositiveCosineProfile20261112 (testDiv)
open OriginalPositiveJacobiAnger20261112 (oddOrder sin_sin)
open OriginalPositiveStripMoments20261112 (m sign coeff summable_coeff integrate_odd)
open OriginalPositiveStripData20261112
open OriginalPositiveCosineInversion20261112 (C)
open OriginalPositiveQuarterContour20261112 (low)
open private div_smooth div_compact from ImbalancedChen.Part3ActualPositiveCosineProfile
open private sin_part from ImbalancedChen.Part3OriginalPositiveStripDensity

def weight (ell : D4→ℤ) (Y : ℝ) (j : ℕ) := 2*m ell Y j*(oddOrder j:ℂ)

theorem weight_sum (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) :
    Summable (fun j => ‖weight ell Y j‖) := by
  simpa only [weight,coeff,sign,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,
    Complex.norm_natCast,Complex.norm_ofNat,pow_one,mul_one,mul_assoc] using
      (summable_coeff ell hY 1 (A:=1) zero_le_one).mul_left 2

private def S (ell : D4→ℤ) (Y θ : ℝ) :=
  (laplace (testDiv ell Y) (Real.sin θ)-laplace (testDiv ell Y) (-(Real.sin θ:ℂ)))/(2*I)

private theorem sine_sum (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (θ : ℝ) :
    HasSum (fun j => 2*m ell Y j*(Real.sin ((oddOrder j:ℝ)*θ):ℂ)) (S ell Y θ) := by
  let f := testDiv ell Y
  have J := integrate_odd ell hY (fun j => 2*(Real.sin ((oddOrder j:ℝ)*θ):ℂ))
    (fun q => (Real.sin (q*Real.sin θ):ℂ)) (C:=2) (R:=1) (by norm_num) zero_le_one
    (fun j => by simpa only [norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,one_pow] using
      mul_le_mul_of_nonneg_left (Real.abs_sin_le_one ((oddOrder j:ℝ)*θ)) (by norm_num : (0:ℝ)≤2)) (fun q _ =>
      (sin_sin q θ).congr_fun (fun j => by ring))
  have e : (∫ q in Ioi (0:ℝ),(Real.sin (q*Real.sin θ):ℂ)*f q)=S ell Y θ := by
    rw [S,div_wave_Ioi ell hY,div_wave_Ioi ell hY,←integral_sub (div_wave_integrable ell hY _)
      (div_wave_integrable ell hY _),div_eq_mul_inv,←integral_mul_const]
    apply integral_congr_ae
    exact ae_of_all _ fun q => by
      rw [Complex.ofReal_sin,Complex.ofReal_mul,Complex.sin]
      rw [show I*(q:ℂ)*(Real.sin θ:ℂ)=((q:ℂ)*Real.sin θ)*I by ring,
        show I*(q:ℂ)*(-(Real.sin θ:ℂ))=-(((q:ℂ)*Real.sin θ)*I) by ring,neg_mul]
      dsimp only [f]; field_simp [I_ne_zero] <;> ring_nf <;> simp [I_sq] <;> ring
  rw [←e]; exact J.congr_fun fun j => by ring

private theorem S_deriv (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (θ : ℝ) :
    HasDerivAt (S ell Y) ((Real.cos θ:ℂ)*C ell hY (Real.sin θ)) θ := by
  let f := testDiv ell Y
  have D (v : ℝ) := (laplace_deriv f (div_smooth ell hY).continuous (div_compact ell hY)
    (by positivity : 0≤16*Y) (fun q h => by
      obtain ⟨a,b⟩ := div_support ell hY (subset_tsupport _ h)
      rwa [abs_of_nonneg (by linarith : 0≤q)]) (v:ℂ)).comp_ofReal
  have pos := (D (Real.sin θ)).comp θ (Real.hasDerivAt_sin θ)
  have neg := (D (-Real.sin θ)).comp θ (Real.hasDerivAt_sin θ).neg
  convert (pos.sub neg).div_const (2*I) using 1
  · funext t; simp [S,f,Function.comp_def]
  · rw [←sin_part ell hY]
    dsimp only [f]; push_cast; field_simp [I_ne_zero] <;> ring

theorem cosine_coefficients (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (θ : ℝ) :
    HasSum (fun j => weight ell Y j*(Real.cos ((oddOrder j:ℝ)*θ):ℂ))
      ((Real.cos θ:ℂ)*C ell hY (Real.sin θ)) := by
  let b := fun j (t : ℝ) => 2*m ell Y j*(Real.sin ((oddOrder j:ℝ)*t):ℂ)
  let d := fun j (t : ℝ) => weight ell Y j*(Real.cos ((oddOrder j:ℝ)*t):ℂ)
  have bound (j : ℕ) (t : ℝ) : ‖d j t‖≤‖weight ell Y j‖ := by
    dsimp only [d]; rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    simpa using mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (norm_nonneg (weight ell Y j))
  have E := hasDerivAt_tsum (g:=b) (g':=d) (weight_sum ell hY)
    (fun j t => by
      convert (((((hasDerivAt_id t).const_mul (oddOrder j:ℝ)).sin).ofReal_comp).const_mul
        (2*m ell Y j)) using 1 <;> dsimp only [b,d,weight] <;> push_cast <;> ring)
    bound (sine_sum ell hY 0).summable θ
  have f : (fun t : ℝ => ∑' j,b j t)=S ell Y := funext fun t => (sine_sum ell hY t).tsum_eq
  rw [f] at E
  exact (Summable.of_norm_bounded (weight_sum ell hY) (fun j => bound j θ)).hasSum_iff.mpr
    (E.unique (S_deriv ell hY θ))

theorem low_integral (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (q : ℝ) :
    HasSum (fun j => weight ell Y j*(low j q:ℂ))
      (∫ s in (0:ℝ)..1,(Real.cos (q*s):ℂ)*C ell hY s) := by
  let V := fun s : ℝ => (Real.cos (q*s):ℂ)*C ell hY s
  let u := fun j t => weight ell Y j*
    ((Real.cos (q*Real.sin t)*Real.cos ((oddOrder j:ℝ)*t):ℝ):ℂ)
  have H := intervalIntegral.hasSum_integral_of_dominated_convergence (μ:=volume) (a:=(0:ℝ)) (b:=Real.pi/2)
    (F:=u) (f:=fun t => Real.cos t • V (Real.sin t)) (fun j _ => ‖weight ell Y j‖)
    (fun j => (by dsimp only [u]; fun_prop : Continuous _).aestronglyMeasurable)
    (fun j => ae_of_all _ fun t _ => by
      simp only [u,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_mul]
      simpa using mul_le_mul_of_nonneg_left
        (mul_le_mul (Real.abs_cos_le_one _) (Real.abs_cos_le_one _) (abs_nonneg _) zero_le_one)
        (norm_nonneg (weight ell Y j)))
    (ae_of_all _ fun _ _ => weight_sum ell hY) intervalIntegrable_const
    (ae_of_all _ fun t _ => by
      have T := (cosine_coefficients ell hY t).mul_left (Real.cos (q*Real.sin t):ℂ)
      convert T using 1
      · funext j; dsimp only [u]; push_cast; ring
      · dsimp only [V]; rw [Complex.real_smul]; ring)
  have sub := intervalIntegral.integral_deriv_smul_comp (g:=V) (a:=(0:ℝ)) (b:=Real.pi/2)
    (fun x _ => Real.hasDerivAt_sin x) Real.continuous_cos.continuousOn
    ((by fun_prop : Continuous (fun s : ℝ => (Real.cos (q*s):ℂ))).mul (C ell hY).continuous)
  change (∫ x in (0:ℝ)..Real.pi/2,Real.cos x • V (Real.sin x))=_ at sub
  rw [Real.sin_zero,Real.sin_pi_div_two] at sub
  rw [←sub]
  apply H.congr_fun
  intro j
  simp only [u,low,intervalIntegral.integral_const_mul,intervalIntegral.integral_ofReal]
end ImbalancedChen.Part3.OriginalPositiveLowCosine20261112
end
