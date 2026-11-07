import ImbalancedChen.Part3ScaledPrimeProfileSW
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual normalized Mellin phase exp(i*t*log(y/U)) has unit norm.
Its first derivative costs |t|/y. A fixed C1 dyadic profile therefore
has Abel variation O_Phi(1+|t|), uniformly in the physical real interval.
There is no claim of an SW estimate uniform over unbounded frequency.
-/

namespace ImbalancedChen.Part3.PrimeMellinProfileVariation20261026b
noncomputable section
open Classical Set MeasureTheory
open scoped BigOperators Topology

def phase (t x : ℝ) : ℂ :=
  Complex.exp (Complex.I*(t : ℂ)*(Real.log x : ℂ))

def profile (Phi : ℝ → ℝ) (t x : ℝ) : ℂ := (Phi x : ℂ)*phase t x
def physicalProfile (Phi : ℝ → ℝ) (t U y : ℝ) : ℂ := profile Phi t (y/U)

theorem phase_norm (t x : ℝ) : ‖phase t x‖ = 1 := by
  rw [phase, Complex.norm_exp]
  simp

theorem phase_hasDerivAt (t : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (phase t) (phase t x*(Complex.I*(t : ℂ)/(x : ℂ))) x := by
  have h := (((Real.hasDerivAt_log hx.ne').ofReal_comp).const_mul
    (Complex.I*(t : ℂ))).cexp
  simpa only [phase, Complex.ofReal_inv, div_eq_mul_inv] using h

theorem profile_hasDerivAt {Phi : ℝ → ℝ} (hPhi : ContDiff ℝ 1 Phi)
    (t : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (profile Phi t)
      (((deriv Phi x : ℂ)+(Phi x : ℂ)*Complex.I*(t : ℂ)/(x : ℂ))*phase t x) x := by
  have hD : Differentiable ℝ Phi := hPhi.differentiable (by norm_num)
  convert ((hD x).hasDerivAt.ofReal_comp).mul (phase_hasDerivAt t hx) using 1 <;>
    simp only [profile] <;> ring

theorem profile_contDiffOn {Phi : ℝ → ℝ} (hPhi : ContDiff ℝ 1 Phi) (t : ℝ) :
    ContDiffOn ℝ 1 (profile Phi t) (Ioi (0 : ℝ)) := by
  intro x hx
  apply ContDiffAt.contDiffWithinAt
  have hl : ContDiffAt ℝ 1 Real.log x := Real.contDiffAt_log.mpr hx.ne'
  have hc : ContDiffAt ℝ 1 (fun y : ℝ => (Real.log y : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hl
  have hp := (hc.const_mul (Complex.I*(t : ℂ))).cexp
  exact (Complex.ofRealCLM.contDiff.comp hPhi).contDiffAt.mul hp

/-- This bound is for the literal complex Mellin profile. In particular
the derivative cost grows linearly with the real frequency. -/
theorem profile_deriv_norm_le {Phi : ℝ → ℝ} (hPhi : ContDiff ℝ 1 Phi)
    {M D : ℝ} (hM : ∀ x ∈ Icc (1 : ℝ) 2, |Phi x| ≤ M)
    (hD : ∀ x ∈ Icc (1 : ℝ) 2, |deriv Phi x| ≤ D)
    (t : ℝ) {x : ℝ} (hx : x ∈ Icc (1 : ℝ) 2) :
    ‖deriv (profile Phi t) x‖ ≤ D+M*|t| := by
  have hx0 : 0 < x := by linarith [hx.1]
  rw [(profile_hasDerivAt hPhi t hx0).deriv, norm_mul, phase_norm, mul_one]
  calc
    _ ≤ ‖(deriv Phi x : ℂ)‖ + ‖(Phi x : ℂ)*Complex.I*(t : ℂ)/(x : ℂ)‖ :=
      norm_add_le _ _
    _ = |deriv Phi x| + |Phi x|*|t|/x := by
      simp only [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_I, mul_one, abs_of_pos hx0]
    _ ≤ |deriv Phi x| + |Phi x|*|t| :=
      add_le_add_left (div_le_self (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hx.1) _
    _ ≤ _ := add_le_add (hD x hx)
      (mul_le_mul_of_nonneg_right (hM x hx) (abs_nonneg _))

private theorem normalized_mem {U u v y : ℝ} (hU : 0 < U)
    (hlo : U ≤ u) (hhi : v ≤ 2*U) (hy : y ∈ Icc u v) : y/U ∈ Icc (1 : ℝ) 2 := by
  exact ⟨(le_div_iff₀ hU).mpr (by linarith [hy.1]),
    (div_le_iff₀ hU).mpr (hy.2.trans hhi)⟩

theorem physicalProfile_contDiffOn {Phi : ℝ → ℝ} (hPhi : ContDiff ℝ 1 Phi)
    (t : ℝ) {U : ℝ} (hU : 0 < U) :
    ContDiffOn ℝ 1 (physicalProfile Phi t U) (Ioi (0 : ℝ)) := by
  apply (profile_contDiffOn hPhi t).comp
    (contDiff_id.div_const U).contDiffOn
  intro y hy
  exact div_pos hy hU

theorem physicalProfile_hasDerivAt {Phi : ℝ → ℝ} (hPhi : ContDiff ℝ 1 Phi)
    (t : ℝ) {U y : ℝ} (hU : 0 < U) (hy : 0 < y) :
    HasDerivAt (physicalProfile Phi t U)
      ((1/U : ℝ) • deriv (profile Phi t) (y/U)) y := by
  have hd := profile_hasDerivAt hPhi t (div_pos hy hU)
  have hp : HasDerivAt (profile Phi t) (deriv (profile Phi t) (y/U)) (y/U) := by
    rwa [hd.deriv]
  simpa only [physicalProfile, Function.comp_def] using
    hp.scomp y ((hasDerivAt_id y).div_const U)

theorem physicalProfile_variation_le {Phi : ℝ → ℝ} (hPhi : ContDiff ℝ 1 Phi)
    {M D U u v : ℝ} (hM0 : 0 ≤ M) (hD0 : 0 ≤ D)
    (hM : ∀ x ∈ Icc (1 : ℝ) 2, |Phi x| ≤ M)
    (hD : ∀ x ∈ Icc (1 : ℝ) 2, |deriv Phi x| ≤ D)
    (hU : 0 < U) (hlo : U ≤ u) (huv : u ≤ v) (hhi : v ≤ 2*U) (t : ℝ) :
    ‖physicalProfile Phi t U v‖ +
      (∫ y in Ioc u v, ‖deriv (physicalProfile Phi t U) y‖) ≤
        (M+D)*(1+|t|) := by
  have hend : ‖physicalProfile Phi t U v‖ ≤ M := by
    simp only [physicalProfile, profile, norm_mul, phase_norm, mul_one,
      Complex.norm_real, Real.norm_eq_abs]
    exact hM _ (normalized_mem hU hlo hhi ⟨huv,le_rfl⟩)
  have hsubset : Icc u v ⊆ Ioi (0 : ℝ) := fun y hy => by
    exact lt_of_lt_of_le hU (hlo.trans hy.1)
  have hcont : ContinuousOn (deriv (physicalProfile Phi t U)) (Icc u v) :=
    ((physicalProfile_contDiffOn hPhi t hU).continuousOn_deriv_of_isOpen
      isOpen_Ioi (by norm_num)).mono hsubset
  have hint : IntegrableOn (fun y => ‖deriv (physicalProfile Phi t U) y‖) (Ioc u v) :=
    hcont.norm.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hconst : IntegrableOn (fun _ : ℝ => (D+M*|t|)/U) (Ioc u v) :=
    continuous_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hpoint (y : ℝ) (hy : y ∈ Ioc u v) :
      ‖deriv (physicalProfile Phi t U) y‖ ≤ (D+M*|t|)/U := by
    have hy0 : 0 < y := lt_of_lt_of_le hU (hlo.trans hy.1.le)
    rw [(physicalProfile_hasDerivAt hPhi t hU hy0).deriv, norm_smul,
      Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hU)]
    calc
      _ ≤ (1/U)* (D+M*|t|) := mul_le_mul_of_nonneg_left
        (profile_deriv_norm_le hPhi hM hD t (normalized_mem hU hlo hhi ⟨hy.1.le,hy.2⟩))
          (one_div_pos.mpr hU).le
      _ = _ := by ring
  have hvariation : (∫ y in Ioc u v, ‖deriv (physicalProfile Phi t U) y‖) ≤ D+M*|t| := by
    calc
      _ ≤ ∫ _y in Ioc u v, (D+M*|t|)/U :=
        setIntegral_mono_on hint hconst measurableSet_Ioc hpoint
      _ = (v-u)*((D+M*|t|)/U) := by
        rw [← intervalIntegral.integral_of_le huv, intervalIntegral.integral_const,
          smul_eq_mul]
      _ ≤ U*((D+M*|t|)/U) := mul_le_mul_of_nonneg_right
        (by linarith : v-u ≤ U) (by positivity)
      _ = D+M*|t| := by field_simp [hU.ne']
  have hDfreq : 0 ≤ D*|t| := mul_nonneg hD0 (abs_nonneg _)
  nlinarith only [hend,hvariation,hDfreq]

end
end ImbalancedChen.Part3.PrimeMellinProfileVariation20261026b
