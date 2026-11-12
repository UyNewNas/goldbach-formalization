import ImbalancedChen.Part3ActualPositiveHolomorphicWeights
import ImbalancedChen.Part3KHeightSchwartz
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Distribution.TemperateGrowth

/-! The ordinary cosine transform of the given test, evaluated on the
positive branch s=cosh u. The resulting function of u is Schwartz. -/
namespace ImbalancedChen.Part3.ActualPositiveCosineProfile20261112

noncomputable section
open Set Filter MeasureTheory Complex FourierTransform
open scoped FourierTransform Topology ContDiff
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest spectralTest_contDiff)
open OriginalFullModulusTestJets20261102 KFullLineFourierBridgeSourceOnly

def testDiv (ell : D4 → ℤ) (Y q : ℝ) : ℂ := spectralTest ell Y q/(q:ℂ)

private theorem div_smooth (ell : D4 → ℤ) {Y : ℝ} (hY : 0<Y) :
    ContDiff ℝ ∞ (testDiv ell Y) := by
  rw [contDiff_iff_contDiffAt]
  intro q
  by_cases z : q=0
  · subst q
    apply (contDiffAt_const (c:=(0:ℂ))).congr_of_eventuallyEq
    filter_upwards [gt_mem_nhds (show (0:ℝ)<Y/16 by positivity)] with q hq
    simp only [testDiv,show spectralTest ell Y q=0 from by
      by_contra h
      exact (not_lt_of_ge (spectralTest_tsupport_strict ell hY (subset_tsupport _ h)).1.le) hq,zero_div]
  · exact (spectralTest_contDiff ell Y).contDiffAt.div (by fun_prop) (Complex.ofReal_ne_zero.mpr z)

private theorem div_compact (ell : D4 → ℤ) {Y : ℝ} (hY : 0<Y) : HasCompactSupport (testDiv ell Y) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc : IsCompact (Icc (Y/16) (16*Y)))
  intro q h
  have nz : spectralTest ell Y q≠0 := fun z => h (by simp [testDiv,z])
  exact ⟨(spectralTest_tsupport_strict ell hY (subset_tsupport _ nz)).1.le,
    (spectralTest_tsupport_strict ell hY (subset_tsupport _ nz)).2.le⟩

private def evenDiv (ell : D4 → ℤ) (Y : ℝ) (q : ℝ) : ℂ :=
  testDiv ell Y q+testDiv ell Y (-q)

private def physical (ell : D4 → ℤ) {Y : ℝ} (hY : 0<Y) : SchwartzMap ℝ ℂ :=
  ((div_compact ell hY).add ((div_compact ell hY).comp_homeomorph (Homeomorph.neg ℝ))).toSchwartzMap
    ((div_smooth ell hY).add ((div_smooth ell hY).comp contDiff_neg))

private def frequency : ℝ ≃L[ℝ] ℝ :=
  ContinuousLinearEquiv.smulLeft (Units.mk0 ((2*Real.pi)⁻¹) (inv_ne_zero (by positivity)))

def cosineTest (ell : D4 → ℤ) {Y : ℝ} (hY : 0<Y) : SchwartzMap ℝ ℂ :=
  (1/2:ℂ) • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ frequency (𝓕 (physical ell hY))

theorem cosineTest_apply (ell : D4 → ℤ) {Y : ℝ} (hY : 0<Y) (s : ℝ) :
    cosineTest ell hY s=∫ q in Ioi (0:ℝ),(Real.cos (q*s):ℂ)*testDiv ell Y q := by
  let F := physical ell hY
  have eq : (F:ℝ → ℂ)=evenDiv ell Y := rfl
  have e := fourier_even_eq_cosine (F:ℝ → ℂ) F.integrable
    (fun q => by rw [eq]; simp only [evenDiv,neg_neg,add_comm]) (frequency s)
  have f : frequency s=s/(2*Real.pi) := by change (2*Real.pi)⁻¹*s=_; ring
  change (1/2:ℂ)*((𝓕 F:SchwartzMap ℝ ℂ):ℝ → ℂ) (frequency s)=_
  rw [SchwartzMap.fourier_coe,e, f,← mul_assoc]
  norm_num
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
  have z : spectralTest ell Y (-q)=0 := by
    by_contra nz
    have L := (spectralTest_tsupport_strict ell hY (subset_tsupport _ nz)).1
    linarith [hq,hY]
  rw [eq,evenDiv,show testDiv ell Y (-q)=0 by simp [testDiv,z],add_zero]
  congr 2
  field_simp [Real.pi_ne_zero] <;> ring

private def X (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ := SchwartzMap.smulLeftCLM ℂ Complex.ofReal f
private def d (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ := SchwartzMap.derivCLM ℂ ℂ f

private theorem X_apply (f : SchwartzMap ℝ ℂ) (s : ℝ) : X f s=(s:ℂ)*f s :=
  SchwartzMap.smulLeftCLM_apply_apply Complex.hasTemperateGrowth_ofReal f s

private def jet (A B : SchwartzMap ℝ ℂ) (u : ℝ) : ℂ :=
  A (Real.cosh u)+(Real.sinh u:ℂ)*B (Real.cosh u)

private theorem jet_deriv (A B : SchwartzMap ℝ ℂ) : deriv (jet A B)=
    jet (X B + X (X (d B)) - d B) (d A) := by
  funext u
  have ha := A.differentiableAt (x:=Real.cosh u)
  have hb := B.differentiableAt (x:=Real.cosh u)
  have D := (ha.hasDerivAt.comp u (Real.hasDerivAt_cosh u)).add
    ((Real.hasDerivAt_sinh u).ofReal_comp.mul (hb.hasDerivAt.comp u (Real.hasDerivAt_cosh u)))
  have sq : (Real.cosh u:ℂ)^2-(Real.sinh u:ℂ)^2=1 := by exact_mod_cast Real.cosh_sq_sub_sinh_sq u
  change deriv (fun v => A (Real.cosh v)+(Real.sinh v:ℂ)*B (Real.cosh v)) u=_
  rw [D.deriv]
  simp only [jet,SchwartzMap.sub_apply,SchwartzMap.add_apply,X_apply,d,SchwartzMap.derivCLM_apply,
    Complex.real_smul]
  linear_combination -(deriv B (Real.cosh u))*sq

private theorem jet_rep (f : SchwartzMap ℝ ℂ) (n : ℕ) :
    ∃ A B : SchwartzMap ℝ ℂ, iteratedDeriv n (fun u => f (Real.cosh u))=jet A B := by
  induction n with
  | zero => exact ⟨f,0,by ext u; simp [jet]⟩
  | succ n ih =>
    obtain ⟨A,B,E⟩ := ih
    exact ⟨_,_,by rw [iteratedDeriv_succ,E,jet_deriv]⟩

/-- At each derivative order the two Schwartz coefficients are evaluated
at cosh u. The second coefficient is multiplied by sinh u. -/
def hyperbolicProfile (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ := by
  refine ⟨fun u => f (Real.cosh u),(f.smooth _).comp Real.contDiff_cosh,?_⟩
  intro k n
  obtain ⟨A,B,E⟩ := jet_rep f n
  refine ⟨SchwartzMap.seminorm ℂ k 0 A+SchwartzMap.seminorm ℂ (k+1) 0 B,fun u => ?_⟩
  have hs : |Real.sinh u|≤Real.cosh u := by
    rw [Real.abs_sinh,← Real.cosh_abs]
    exact (Real.sinh_lt_cosh _).le
  have hu : |u|≤Real.cosh u :=
    (Real.self_le_sinh_iff.mpr (abs_nonneg u)).trans ((Real.abs_sinh u).symm.le.trans hs)
  have a := SchwartzMap.le_seminorm' ℂ k 0 A (Real.cosh u)
  have b := SchwartzMap.le_seminorm' ℂ (k+1) 0 B (Real.cosh u)
  simp only [Real.norm_eq_abs,abs_of_pos (Real.cosh_pos _),iteratedDeriv_zero] at a b
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,E,Real.norm_eq_abs]
  calc
    _ ≤ (Real.cosh u)^k*(‖A (Real.cosh u)‖+Real.cosh u*‖B (Real.cosh u)‖) := by
      apply mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hu k) _ (norm_nonneg _) (pow_nonneg (Real.cosh_pos _).le _)
      exact (norm_add_le _ _).trans (add_le_add_left (by
        rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right hs (norm_nonneg _)) _)
    _ ≤ _ := by rw [pow_succ] at b; linarith only [a,b]

def profile (ell : D4 → ℤ) {Y : ℝ} (hY : 0<Y) : SchwartzMap ℝ ℂ :=
  hyperbolicProfile (cosineTest ell hY)

@[simp] theorem profile_apply (ell : D4 → ℤ) {Y : ℝ} (hY : 0<Y) (u : ℝ) :
    profile ell hY u=cosineTest ell hY (Real.cosh u) := rfl

theorem weighted_profile_L1 (ell : D4 → ℤ) {Y : ℝ} (hY : 0<Y) :
    Integrable (fun u => Real.cosh u*‖profile ell hY u‖) := by
  have H := (hyperbolicProfile (X (cosineTest ell hY))).integrable.norm
  convert H using 1
  funext u
  change Real.cosh u*‖cosineTest ell hY (Real.cosh u)‖=‖X (cosineTest ell hY) (Real.cosh u)‖
  rw [X_apply,norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.cosh_pos _).le]

end
end ImbalancedChen.Part3.ActualPositiveCosineProfile20261112

