import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

/-! Causal inverse for the order one-half kernel which occurs in the
fixed negative Bruhat orbit. All convolution identities are pointwise. -/
namespace ImbalancedChen.Part3.OriginalAbelKernel
noncomputable section
open Set Filter MeasureTheory Complex ContinuousLinearMap
open scoped ContDiff Convolution Topology

def K (u : ℝ) : ℝ := if 0<u then Real.exp (-u)/Real.sqrt u else 0
def E (u : ℝ) : ℝ := if 0<u then Real.exp (-u) else 0
def A (D : ℝ → ℂ) : ℝ → ℂ := convolution K D (lsmul ℝ ℝ) volume

theorem K_nonneg (u : ℝ) : 0≤K u := by unfold K; split <;> positivity

theorem K_integrable : Integrable K := by
  have I := (Real.GammaIntegral_convergent (s := (1/2:ℝ)) (by norm_num)).integrable_indicator
    measurableSet_Ioi
  apply I.congr
  filter_upwards with u
  by_cases h : 0<u
  · rw [indicator_of_mem h, K, if_pos h, show (1/2:ℝ)-1= -(1/2:ℝ) by norm_num,
      Real.rpow_neg h.le,←Real.sqrt_eq_rpow, div_eq_mul_inv]
  · simp [K,h,Set.mem_Ioi] at *

private lemma half_beta (q : ℝ) (hq : 0<q) :
    (∫ u in Ioo (0:ℝ) q, (Real.sqrt u)⁻¹ * (Real.sqrt (q-u))⁻¹) = Real.pi := by
  let s : ℂ := 1/2
  have hs : 0<s.re := by norm_num [s]
  have hg := Complex.Gamma_mul_Gamma_eq_betaIntegral hs hs
  have hsum : s+s=1 := by norm_num [s]
  have hγ : Complex.Gamma s = (Real.sqrt Real.pi : ℝ) := by
    rw [show s=((1/2:ℝ):ℂ) by norm_num [s],Complex.Gamma_ofReal,Real.Gamma_one_half_eq]
  rw [hsum,Complex.Gamma_one,hγ,one_mul] at hg
  have b := Complex.betaIntegral_scaled s s hq
  rw [hsum,sub_self,Complex.cpow_zero,one_mul,←hg] at b
  have B : (Real.sqrt Real.pi : ℂ)*(Real.sqrt Real.pi:ℂ)=(Real.pi:ℂ) := by
    exact_mod_cast Real.mul_self_sqrt Real.pi_pos.le
  rw [B,intervalIntegral.integral_of_le hq.le,integral_Ioc_eq_integral_Ioo] at b
  apply Complex.ofReal_injective
  rw [←integral_ofReal,←b]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro u hu
  have powr (x : ℝ) (hx : 0<x) :
      ((Real.sqrt x)⁻¹:ℝ)=(x ^ (-(1/2:ℝ))) := by
    rw [Real.rpow_neg hx.le,Real.sqrt_eq_rpow]
  rw [powr _ hu.1,powr _ (sub_pos.mpr hu.2),Complex.ofReal_mul,
    Complex.ofReal_cpow hu.1.le,Complex.ofReal_cpow (sub_nonneg.mpr hu.2.le)]
  push_cast
  norm_num [s]

theorem square_kernel (q : ℝ) :
    (K ⋆ K) q=Real.pi*E q := by
  change (∫u:ℝ,K u*K (q-u))=_
  have on (u : ℝ) : K u*K (q-u) =
      (Ioo (0:ℝ) q).indicator
        (fun u => Real.exp (-q)*((Real.sqrt u)⁻¹*(Real.sqrt (q-u))⁻¹)) u := by
    by_cases h : 0<u ∧ u<q
    · rw [indicator_of_mem h,K,K,if_pos h.1,if_pos (sub_pos.mpr h.2),
        show -q= -u + -(q-u) by ring,Real.exp_add]
      ring
    · rw [indicator_of_notMem h]
      rcases not_and_or.mp h with h|h
      · simp [K,h]
      · have t : ¬0<q-u := by linarith
        simp [K,t]
  simp_rw [on]
  rw [integral_indicator measurableSet_Ioo,integral_const_mul]
  by_cases hp : 0<q
  · rw [half_beta q hp,E,if_pos hp,mul_comm]
  · simp [Ioo_eq_empty_of_le (le_of_not_gt hp),E,hp]

private lemma A_twice (D : ℝ→ℂ) (hD : Continuous D) (hc : HasCompactSupport D) (q : ℝ) :
    A (A D) q= ∫u:ℝ, (Real.pi * E (q-u)) • D u := by
  obtain ⟨C,hC⟩ := hD.norm.bddAbove_range_of_hasCompactSupport hc.norm
  have bound (x : ℝ) : ‖D x‖ ≤ C := hC (Set.mem_range_self x)
  let L : ℝ →L[ℝ] ℂ →L[ℝ] ℂ := lsmul ℝ ℝ
  have hg := hc.convolutionExists_right L K_integrable.locallyIntegrable hD
  have hkk := K_integrable.ae_convolution_exists (lsmul ℝ ℝ (E := ℝ)) K_integrable
  have hi : Integrable (Function.uncurry fun x y : ℝ => K y • (K (x-y) • D (q-x))) (volume.prod volume) := by
    have prodI := K_integrable.convolution_integrand (lsmul ℝ ℝ (E := ℝ)) K_integrable
    apply (prodI.norm.mul_const C).mono'
    · have km : Measurable K := by unfold K; fun_prop
      dsimp only [Function.uncurry]; fun_prop
    · filter_upwards with v
      simp only [Function.uncurry_apply_pair,norm_smul,lsmul_apply,smul_eq_mul,norm_mul]
      grw [bound]; ring_nf
  have T := convolution_assoc' (lsmul ℝ ℝ (E := ℝ)) L L L
    (fun x y z => (smul_smul x y z).symm) (x₀ := q) hkk
    (ae_of_all _ hg) hi
  change A (A D) q=_
  rw [←T,convolution_lsmul_swap]
  simp_rw [square_kernel]

def D (F : ℝ→ℂ) (p : ℝ) := deriv F p+F p
def inverse (F : ℝ→ℂ) (p : ℝ) := (Real.pi : ℂ)⁻¹ * A (D F) p

lemma D_smooth {F : ℝ→ℂ} (h : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (D F) :=
  (contDiff_infty_iff_deriv.mp h).2.add h

lemma D_compact {F : ℝ→ℂ} (h : HasCompactSupport F) : HasCompactSupport (D F) :=
  h.deriv.add h

/-- The right-hand derivative acts on the original smooth test. Neither
the singular kernel nor a moving endpoint is differentiated. -/
theorem invert {F : ℝ→ℂ} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (q : ℝ) :
    A (inverse F) q=F q := by
  let G : ℝ→ℂ := fun u => (Real.exp u : ℂ)*F u
  have hG : ContDiff ℝ 1 G := by dsimp [G]; fun_prop
  have cG : HasCompactSupport G := hc.mul_left
  have dG (u : ℝ) : deriv G u=(Real.exp u : ℂ)*D F u := by
    have a := (Real.hasDerivAt_exp u).ofReal_comp
    have b := (hF.differentiable (by simp) u).hasDerivAt
    rw [show deriv G u=_ from (a.mul b).deriv]
    simp only [D]; ring
  have integ := HasCompactSupport.integral_Iic_deriv_eq hG cG q
  simp_rw [dG] at integ
  have cutoff (u : ℝ) : (Real.pi*E (q-u)) • D F u =
      (Iio q).indicator (fun u => (Real.pi*Real.exp (-q):ℝ) • ((Real.exp u : ℂ)*D F u)) u := by
    by_cases h : u<q
    · rw [indicator_of_mem h,E,if_pos (sub_pos.mpr h),neg_sub,sub_eq_add_neg,Real.exp_add]
      simp only [Complex.real_smul,Complex.ofReal_mul]; ring
    · simp [E,not_lt.mpr (sub_nonpos.mpr (le_of_not_gt h)),indicator_of_notMem h]
  have S := A_twice (D F) (D_smooth hF).continuous (D_compact hc) q
  simp_rw [cutoff] at S
  rw [integral_indicator measurableSet_Iio,←integral_Iic_eq_integral_Iio,
    integral_smul,integ] at S
  change (∫u:ℝ,K u • ((Real.pi:ℂ)⁻¹ * A (D F) (q-u)))=_
  have pull (u : ℝ) : K u • ((Real.pi:ℂ)⁻¹*A (D F) (q-u)) =
      (Real.pi:ℂ)⁻¹*(K u • A (D F) (q-u)) := by simp only [Complex.real_smul]; ring
  simp_rw [pull,integral_const_mul]
  change (Real.pi:ℂ)⁻¹ * A (A (D F)) q=_
  rw [S]
  simp [Complex.real_smul,G,Real.exp_neg,Real.pi_ne_zero,Real.exp_ne_zero,mul_assoc]

end
end ImbalancedChen.Part3.OriginalAbelKernel
