import ImbalancedChen.Part3ActualEisensteinReciprocalGrowth
import ImbalancedChen.Part3ActualOrdinaryContinuousModes
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

/-! Growth in height of the scalar taking each actual completed Young
oldform to its ordinary normalization in the contour strip. -/
namespace ImbalancedChen.Part3.ActualEisensteinOrdinaryGrowth20261110

noncomputable section
open Set Complex MeasureTheory
open ActualCharacterCriticalFamily20261110 ActualCharacterPoissonRows20261110
open ActualOrdinaryContinuousModes20261110 ActualEisensteinReciprocalGrowth20261110

private theorem gamma_majorant {z : ℂ} (hz : 0 < z.re) :
    ‖Complex.Gamma z‖ ≤ Real.Gamma z.re := by
  rw [Complex.Gamma_eq_integral hz,Complex.GammaIntegral,Real.Gamma_eq_integral hz]
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  rw [norm_mul,Complex.norm_of_nonneg (Real.exp_pos _).le,Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

private theorem sin_bound (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  have H := norm_sub_le (Complex.exp (-z*I)) (Complex.exp (z*I))
  rw [Complex.norm_exp,Complex.norm_exp] at H
  simp only [neg_mul,Complex.neg_re,Complex.mul_I_re,neg_neg] at H
  rw [Complex.sin,norm_div,norm_mul,Complex.norm_I,mul_one,Complex.norm_ofNat]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  linarith [Real.exp_le_exp.mpr (le_abs_self z.im),Real.exp_le_exp.mpr (neg_le_abs z.im)]

/-- A rough exponential bound suffices because the contour multiplier
has Gaussian decay. Reflection gives this bound without invoking a
uniform asymptotic for the Gamma function. -/
theorem gamma_inverse_strip :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℂ, 1/2 ≤ s.re → s.re ≤ 3/2 → 1 ≤ |s.im| →
      ‖(Complex.Gamma s)⁻¹‖ ≤ B*Real.exp (Real.pi*|s.im|) := by
  have CC : ContinuousOn Real.Gamma (Icc (1/2 : ℝ) (3/2)) := by
    apply Real.differentiableOn_Gamma_Ioi.continuousOn.mono
    intro x hx
    exact (by linarith [hx.1] : 0 < x)
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn CC
  refine ⟨max C 0/Real.pi,div_nonneg (le_max_right _ _) Real.pi_pos.le,?_⟩
  intro s hs ht him
  have h2 : 0 < (2-s).re := by simp only [Complex.sub_re,Complex.re_ofNat]; linarith
  have hΓ := Complex.Gamma_ne_zero_of_re_pos (by linarith : 0 < s.re)
  have hW : 1 ≤ ‖1-s‖ := him.trans (by simpa using Complex.abs_im_le_norm (1-s))
  have hV : (1-s : ℂ) ≠ 0 := fun e => (by simp [e] at hW)
  have recu : Complex.Gamma (2-s) = (1-s)*Complex.Gamma (1-s) := by
    simpa only [show (1-s)+1=2-s by ring] using Complex.Gamma_add_one (1-s) hV
  have hb : ‖Complex.Gamma (1-s)‖ ≤ max C 0 := by
    have H : (2-s).re ∈ Icc (1/2 : ℝ) (3/2) := by
      simp only [Complex.sub_re,Complex.re_ofNat,mem_Icc]
      constructor <;> linarith
    have H' := (gamma_majorant h2).trans ((le_abs_self _).trans
      (by simpa [Real.norm_eq_abs] using hC (2-s).re H))
    rw [recu,norm_mul] at H'
    exact (le_mul_of_one_le_left (norm_nonneg _) hW).trans (H'.trans (le_max_left _ _))
  have hG1 : Complex.Gamma (1-s) ≠ 0 := by
    intro e
    exact Complex.Gamma_ne_zero_of_re_pos h2 (by simpa [e] using recu)
  have R := Complex.Gamma_mul_Gamma_one_sub s
  have hsin : Complex.sin ((Real.pi : ℂ)*s) ≠ 0 := by
    intro e
    exact (mul_ne_zero hΓ hG1) (by simpa [e] using R)
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have E : (Complex.Gamma s)⁻¹ =
      Complex.Gamma (1-s)*Complex.sin ((Real.pi : ℂ)*s)/(Real.pi : ℂ) := by
    have H := (eq_div_iff hsin).mp R
    field_simp [hΓ,hpi]
    linear_combination -H
  have hsinB := sin_bound ((Real.pi : ℂ)*s)
  simp only [Complex.im_ofReal_mul,abs_mul,abs_of_pos Real.pi_pos] at hsinB
  rw [E,norm_div,norm_mul,Complex.norm_of_nonneg Real.pi_pos.le]
  calc
    _ ≤ (max C 0*Real.exp (Real.pi*|s.im|))/Real.pi :=
      div_le_div_of_nonneg_right (mul_le_mul hb hsinB (norm_nonneg _) (le_max_right _ _)) Real.pi_pos.le
    _ = _ := by ring

private theorem pi_power_le {s : ℂ} (h : s.re ≤ 3/2) :
    ‖(Real.pi : ℂ)^s‖ ≤ Real.pi^(3/2 : ℝ) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  exact Real.rpow_le_rpow_of_exponent_le (by linarith [Real.one_le_pi_div_two]) h

/-- Both ordinary factors are the ones used on the physical principal
and nonprincipal dilations. The only pole-like loss towards the left
edge is the first power of Re(s)-1/2. -/
theorem original_ordinary_factors {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 1/2 < s.re → s.re ≤ 3/2 → 1 ≤ |s.im| →
      (s.re-1/2)*‖uncompletionFactor χ s‖ ≤ C*Real.exp (Real.pi*|s.im|) ∧
      (s.re-1/2)*‖principalFactor s‖ ≤ C*Real.exp (Real.pi*|s.im|) := by
  obtain ⟨B,hB,H⟩ := gamma_inverse_strip
  obtain ⟨D,hD,J⟩ := relative_reciprocal_bound
  let P := Real.pi^(3/2 : ℝ)
  let c := max ‖gauss χ‖ 1
  have hc : 1 ≤ c := le_max_right _ _
  have hP : 0 ≤ P := Real.rpow_nonneg Real.pi_pos.le _
  refine ⟨P*c*B*D,by positivity,?_⟩
  intro s hs ht hy
  have hq : 1 ≤ (q : ℝ) := by exact_mod_cast (NeZero.one_le : 1 ≤ q)
  have hqpow : 1 ≤ ‖(q : ℂ)^s‖ := by
    rw [← Complex.ofReal_natCast,Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < (q : ℝ))]
    exact Real.one_le_rpow hq (by linarith)
  have J₁ := J q (χ^2) s hs ht
  have J₂ := J 1 (1 : DirichletCharacter ℂ 1) s hs ht
  have G := H s hs.le ht hy
  have Z : ‖(Real.pi : ℂ)^s‖ ≤ P := pi_power_le ht
  have V := mul_le_mul ((div_le_self (norm_nonneg ((Real.pi : ℂ)^s)) hqpow).trans Z)
    (le_max_left ‖gauss χ‖ 1) (norm_nonneg _) hP
  have H₁ := mul_le_mul (mul_le_mul V G (norm_nonneg _) (mul_nonneg hP (zero_le_one.trans hc)))
    J₁ (mul_nonneg (sub_nonneg.mpr hs.le) (norm_nonneg _)) (by positivity)
  have H₂ := mul_le_mul (mul_le_mul (Z.trans (le_mul_of_one_le_right hP hc)) G
    (norm_nonneg _) (by positivity : 0 ≤ P*c)) J₂
    (mul_nonneg (sub_nonneg.mpr hs.le) (norm_nonneg _)) (by positivity)
  simp only [uncompletionFactor,principalFactor,div_eq_mul_inv,norm_mul,norm_inv] at *
  constructor
  · convert H₁ using 1 <;> unfold c at * <;> ring
  · convert H₂ using 1 <;> ring

end
end ImbalancedChen.Part3.ActualEisensteinOrdinaryGrowth20261110
