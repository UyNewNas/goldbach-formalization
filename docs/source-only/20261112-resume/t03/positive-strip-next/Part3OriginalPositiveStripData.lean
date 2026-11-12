import ImbalancedChen.Part3OriginalPositiveJacobiAnger
import ImbalancedChen.Part3ActualPositiveCosineProfile
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Batteries.Tactic.OpenPrivate

/-! The prescribed positive compact input and its compact Fourier--Laplace integral.
One integration by parts is uniform in the closed upper half-plane. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalPositiveStripData20261112
open Set Filter MeasureTheory Complex Metric
open scoped Topology ContDiff BigOperators
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest spectralTest_contDiff)
open OriginalFullModulusTestJets20261102 (spectralTest_tsupport_strict)
open ActualPositiveCosineProfile20261112 (testDiv)
open ActualPositiveHolomorphicWeights20261112 (intJ moment expMass intJ_bound moment_L1 moment_factorial)
open OriginalPositiveJacobiAnger20261112 (oddOrder)
open private div_smooth div_compact from ImbalancedChen.Part3ActualPositiveCosineProfile

def laplace (f : ℝ→ℂ) (v : ℂ) := ∫ q : ℝ, f q*Complex.exp (I*(q:ℂ)*v)

theorem laplace_deriv (f : ℝ→ℂ) (hf : Continuous f) (hc : HasCompactSupport f)
    {D : ℝ} (hD : 0≤D) (hS : ∀ q∈Function.support f,|q|≤D) (v : ℂ) :
    HasDerivAt (laplace f) (laplace (fun q => f q*(I*q)) v) v := by
  let F := fun (t : ℂ) (q : ℝ) => f q*Complex.exp (I*q*t)
  let G := fun (t : ℂ) (q : ℝ) => (f q*(I*q))*Complex.exp (I*q*t)
  let A := D*Real.exp (D*(‖v‖+1))
  have hi (t : ℂ) : Integrable (F t) :=
    (hf.mul (by dsimp [F]; fun_prop)).integrable_of_hasCompactSupport hc.mul_right
  have hd (q : ℝ) (t : ℂ) : HasDerivAt (fun w => F w q) (G t q) t := by
    convert (((hasDerivAt_id t).const_mul (I*(q:ℂ))).cexp.const_mul (f q)) using 1 <;>
      dsimp [F,G] <;> ring
  have H := hasDerivAt_integral_of_dominated_loc_of_deriv_le (F:=F) (F':=G)
    (bound:=fun q => A*‖f q‖) (Metric.ball_mem_nhds v (by norm_num : (0:ℝ)<1))
    (Eventually.of_forall fun t => (hi t).aestronglyMeasurable) (hi v)
    (show Continuous (G v) by dsimp [G]; fun_prop).aestronglyMeasurable
  apply (H _ ((hf.integrable_of_hasCompactSupport hc).norm.const_mul A)
    (ae_of_all _ (fun q t _ => hd q t))).2
  exact ae_of_all _ fun q t ht => by
    by_cases z : f q=0
    · simp [G,z]
    have qa := hS q z
    have tv : ‖t‖≤‖v‖+1 := by
      have := norm_le_norm_add_norm_sub' t v
      linarith [Metric.mem_ball.mp ht,dist_eq_norm t v]
    have e : (I*(q:ℂ)*t).re≤D*(‖v‖+1) := by
      apply (Complex.re_le_norm _).trans
      simpa [norm_mul] using mul_le_mul qa tv (norm_nonneg _) hD
    simp only [G,norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_exp]
    dsimp only [A]
    nlinarith only [mul_le_mul_of_nonneg_left
      (mul_le_mul qa (Real.exp_le_exp.mpr e) (Real.exp_pos _).le hD) (norm_nonneg (f q))]

theorem laplace_parts {f : ℝ→ℂ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (v : ℂ) :
    (I*v)*laplace f v = -laplace (deriv f) v := by
  let E := fun x : ℝ => Complex.exp (I*x*v)
  have hE (x : ℝ) : HasDerivAt E ((I*v)*E x) x := by
    convert (((hasDerivAt_id (x:=(x:ℂ))).const_mul (I*v)).cexp.comp_ofReal) using 1 <;>
      first | funext t; dsimp [E]; ring_nf | dsimp [E]; ring
  have A := integral_mul_deriv_eq_deriv_mul_of_integrable (u:=f) (v:=E)
    (u':=deriv f) (v':=fun x => (I*v)*E x)
    (fun x _ => (hf.differentiable (by simp) x).hasDerivAt) (fun x _ => hE x)
    ((hf.continuous.mul (by dsimp [E]; fun_prop)).integrable_of_hasCompactSupport hc.mul_right)
    (((hf.continuous_deriv (by simp)).mul (by dsimp [E]; fun_prop)).integrable_of_hasCompactSupport hc.deriv.mul_right)
    ((hf.continuous.mul (by dsimp [E]; fun_prop)).integrable_of_hasCompactSupport hc.mul_right)
  simp_rw [mul_left_comm (f _) (I*v)] at A
  simpa only [integral_const_mul,laplace,E] using A

theorem laplace_bound {f : ℝ→ℂ} (hf : Continuous f) (hc : HasCompactSupport f)
    (pos : ∀ q∈Function.support f,0≤q) {v : ℂ} (hv : 0≤v.im) :
    ‖laplace f v‖ ≤ ∫ q : ℝ, ‖f q‖ := by
  apply norm_integral_le_of_norm_le (hf.integrable_of_hasCompactSupport hc).norm
  exact ae_of_all _ fun q => by
    by_cases z : f q=0
    · simp [z]
    rw [norm_mul,Complex.norm_exp]
    have a : (Complex.I*(q:ℂ)*v).re≤0 := by
      simpa [Complex.mul_re,Complex.mul_im] using neg_nonpos.mpr (mul_nonneg (pos q z) hv)
    simpa using mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr a) (norm_nonneg (f q))

theorem laplace_decay {f : ℝ→ℂ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (pos : ∀ q∈tsupport f,0≤q) {v : ℂ} (hv : 0≤v.im) :
    ‖v‖*‖laplace f v‖ ≤ ∫ q : ℝ,‖deriv f q‖ := by
  have e := congrArg norm (laplace_parts hf hc v)
  rw [norm_mul,norm_mul,Complex.norm_I,one_mul,norm_neg] at e
  exact e.le.trans (laplace_bound (hf.continuous_deriv (by simp)) hc.deriv
    (fun q h => pos q (support_deriv_subset h)) hv)

theorem div_support (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) :
    tsupport (testDiv ell Y)⊆Icc (Y/16) (16*Y) := by
  apply closure_minimal _ isClosed_Icc
  intro q h
  have nz : spectralTest ell Y q≠0 := fun hq => h (by simp [testDiv,hq])
  exact ⟨(spectralTest_tsupport_strict ell hY (subset_tsupport _ nz)).1.le,
    (spectralTest_tsupport_strict ell hY (subset_tsupport _ nz)).2.le⟩

theorem div_laplace_diff (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) :
    Differentiable ℂ (laplace (testDiv ell Y)) := fun v =>
  (laplace_deriv _ (div_smooth ell hY).continuous (div_compact ell hY)
    (by positivity : 0≤16*Y) (fun q h => by
      obtain ⟨a,b⟩ := div_support ell hY (subset_tsupport _ h)
      rwa [abs_of_nonneg (by linarith : 0≤q)]) v).differentiableAt

theorem div_laplace_bounds (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) :
    ∃ C : ℝ,0≤C ∧ ∀ v : ℂ,0≤v.im →
      ‖laplace (testDiv ell Y) v‖≤C ∧ ‖v‖*‖laplace (testDiv ell Y) v‖≤C := by
  let f := testDiv ell Y
  let A := ∫ q : ℝ, ‖f q‖
  let D := ∫ q : ℝ, ‖deriv f q‖
  have ha : 0≤A := integral_nonneg fun _ => norm_nonneg _
  have hd : 0≤D := integral_nonneg fun _ => norm_nonneg _
  have p (q : ℝ) (h : q∈tsupport f) : 0≤q := by have := (div_support ell hY h).1; linarith
  refine ⟨A+D,by positivity,fun v hv => ⟨?_,?_⟩⟩
  · exact (laplace_bound (div_smooth ell hY).continuous (div_compact ell hY)
      (fun q h => p q (subset_tsupport _ h)) hv).trans (le_add_of_nonneg_right hd)
  · exact (laplace_decay (div_smooth ell hY) (div_compact ell hY) p hv).trans (le_add_of_nonneg_left ha)

theorem div_wave_Ioi (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (v : ℂ) :
    laplace (testDiv ell Y) v=∫ q in Ioi (0:ℝ),testDiv ell Y q*Complex.exp (I*q*v) := by
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro q hq
  have h : testDiv ell Y q=0 := by
    by_contra z
    have := (div_support ell hY (subset_tsupport _ z)).1
    exact hq (by change 0<q; linarith)
  simp [h]

theorem div_wave_integrable (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (v : ℂ) :
    IntegrableOn (fun q : ℝ => testDiv ell Y q*Complex.exp (I*q*v)) (Ioi 0) :=
  (((div_smooth ell hY).continuous.mul (by fun_prop)).integrable_of_hasCompactSupport
    (div_compact ell hY).mul_right).integrableOn

end ImbalancedChen.Part3.OriginalPositiveStripData20261112
end
