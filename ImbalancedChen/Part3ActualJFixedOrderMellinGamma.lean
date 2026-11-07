import ImbalancedChen.Part3ActualJMellinAngularGammaValue
import ImbalancedChen.Part3JMellinGammaParity

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

Actual full fixed-order J Mellin evaluation in 0<Re(s)<1/2. The actual
integral has already been reduced and evaluated by honest Abel removal,
Poisson Fubini, principal imaginary-axis phases, and a complex Beta moment.
Euler reflection and Legendre duplication now simplify that actual Gamma
product to the prospective ratio, proving its identification rather than
assuming it. Original automorphic normalization remains OPEN.
-/

namespace ImbalancedChen.Part3.ActualJFixedOrderMellinGamma20261026b

noncomputable section
open Complex
open ActualJCriticalLogBound20261026a ActualJFixedOrderMellinL120261026b
open ActualJMellinPoissonGammaReduction20261026b ActualJMellinAngularGammaValue20261026b
open JMellinGammaParity20261026b

/-- Exact duplication/reflection cancellation in the initial Mellin strip. -/
theorem cosine_Gamma_half_product {a : ℂ} (ha0 : 0 < a.re) (ha1 : a.re < 1) :
    Complex.cos ((Real.pi : ℂ) * a / 2) * Gamma a * Gamma ((1 - a) / 2) =
      (2 : ℂ) ^ (a - 1) * (Real.sqrt Real.pi : ℂ) * Gamma (a / 2) := by
  have hz : 0 < ((1 - a) / 2).re := by
    simpa using (show 0 < (1 - a.re) / 2 by linarith)
  have hh : 0 < (a / 2 + 1 / 2).re := by
    simpa using (show 0 < a.re / 2 + 1 / 2 by linarith)
  have hGz := Gamma_ne_zero_of_re_pos hz
  have hGh := Gamma_ne_zero_of_re_pos hh
  have hsine : Complex.sin ((Real.pi : ℂ) * ((1 - a) / 2)) =
      Complex.cos ((Real.pi : ℂ) * a / 2) := by
    rw [show (Real.pi : ℂ) * ((1 - a) / 2) =
      (Real.pi : ℂ) / 2 - (Real.pi : ℂ) * a / 2 by ring, Complex.sin_sub]
    simp
  have href := Gamma_mul_Gamma_one_sub ((1 - a) / 2)
  rw [show 1 - (1 - a) / 2 = a / 2 + 1 / 2 by ring, hsine] at href
  have hc : Complex.cos ((Real.pi : ℂ) * a / 2) ≠ 0 := by
    intro hzero
    rw [hzero, div_zero] at href
    exact mul_ne_zero hGz hGh href
  have href' : Gamma ((1 - a) / 2) * Gamma (a / 2 + 1 / 2) *
      Complex.cos ((Real.pi : ℂ) * a / 2) = (Real.pi : ℂ) := (eq_div_iff hc).1 href
  have hdup : Gamma (a / 2) * Gamma (a / 2 + 1 / 2) =
      Gamma a * (2 : ℂ) ^ (1 - a) * (Real.sqrt Real.pi : ℂ) := by
    simpa only [show (2 : ℂ) * (a / 2) = a by ring] using
      Gamma_mul_Gamma_add_half (a / 2)
  have hp : (2 : ℂ) ^ (a - 1) * (2 : ℂ) ^ (1 - a) = 1 := by
    rw [← Complex.cpow_add (a - 1) (1 - a) (by norm_num : (2 : ℂ) ≠ 0),
      show (a - 1) + (1 - a) = 0 by ring, Complex.cpow_zero]
  have hsq : (Real.sqrt Real.pi : ℂ) ^ 2 = (Real.pi : ℂ) := by
    exact_mod_cast Real.sq_sqrt Real.pi_pos.le
  apply (mul_right_cancel₀ hGh)
  calc
    (Complex.cos ((Real.pi : ℂ) * a / 2) * Gamma a * Gamma ((1 - a) / 2)) *
        Gamma (a / 2 + 1 / 2) =
      Gamma a * (Gamma ((1 - a) / 2) * Gamma (a / 2 + 1 / 2) *
        Complex.cos ((Real.pi : ℂ) * a / 2)) := by ring
    _ = Gamma a * (Real.pi : ℂ) := by rw [href']
    _ = ((2 : ℂ) ^ (a - 1) * (Real.sqrt Real.pi : ℂ) * Gamma (a / 2)) *
        Gamma (a / 2 + 1 / 2) := by
      symm
      calc
        _ = (2 : ℂ) ^ (a - 1) * (Gamma (a / 2) * Gamma (a / 2 + 1 / 2)) *
            (Real.sqrt Real.pi : ℂ) := by ring
        _ = (2 : ℂ) ^ (a - 1) *
            (Gamma a * (2 : ℂ) ^ (1 - a) * (Real.sqrt Real.pi : ℂ)) *
            (Real.sqrt Real.pi : ℂ) := by rw [hdup]
        _ = Gamma a * ((2 : ℂ) ^ (a - 1) * (2 : ℂ) ^ (1 - a)) *
            (Real.sqrt Real.pi : ℂ) ^ 2 := by ring
        _ = _ := by rw [hp, hsq]; ring

theorem poissonGammaValue_eq_jImaginaryGammaRatio {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) (t : ℝ) :
    poissonMellinConstant t * angularBoundaryGammaValue s t = jImaginaryGammaRatio s t := by
  let nu : ℂ := 2 * I * (t : ℂ)
  let a : ℂ := s + nu
  have hre : a.re = s.re := by dsimp [a, nu]; simp
  have hprod := cosine_Gamma_half_product
    (a := a) (by rw [hre]; exact hs0) (by rw [hre]; exact hs1)
  have hS : (Real.sqrt Real.pi : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 Real.pi_pos).ne'
  have hGnu : Gamma (nu + 1 / 2) ≠ 0 := Gamma_ne_zero_of_re_pos (by dsimp [nu]; norm_num)
  have hden : (1 - a) / 2 + nu + 1 / 2 = 1 - s / 2 + I * (t : ℂ) := by
    dsimp [a, nu]
    ring
  have hhalf : a / 2 = s / 2 + I * (t : ℂ) := by dsimp [a, nu]; ring
  have hGden : Gamma ((1 - a) / 2 + nu + 1 / 2) ≠ 0 := by
    apply Gamma_ne_zero_of_re_pos
    rw [hden]
    have hh : 0 < 1 - s.re / 2 := by linarith
    simpa using hh
  have hpowers : (2 : ℂ) ^ (-nu) * (2 : ℂ) ^ (a - 1) = (2 : ℂ) ^ (s - 1) := by
    rw [← Complex.cpow_add (-nu) (a - 1) (by norm_num : (2 : ℂ) ≠ 0)]
    congr 1
    dsimp [a]
    ring
  change ((2 : ℂ) ^ (-nu) * ((Real.sqrt Real.pi : ℂ) * Gamma (nu + 1 / 2))⁻¹) *
      ((Complex.cos ((Real.pi : ℂ) * a / 2) * Gamma a * Gamma ((1 - a) / 2)) *
        Gamma (nu + 1 / 2) / Gamma ((1 - a) / 2 + nu + 1 / 2)) = _
  rw [hprod]
  calc
    _ = ((2 : ℂ) ^ (-nu) * (2 : ℂ) ^ (a - 1)) * Gamma (a / 2) /
        Gamma ((1 - a) / 2 + nu + 1 / 2) := by
      field_simp [hS, hGnu, hGden] <;> ring
    _ = jImaginaryGammaRatio s t := by
      rw [hpowers, hhalf, hden]
      rfl

/-- The actual literal J_(2it) Mellin integral equals the classical Gamma
ratio. This is proved from actual integrals, not an identification premise. -/
theorem actualJMellinIntegral_eq_gamma_ratio {s : ℂ}
    (hs0 : 0 < s.re) (hsHalf : s.re < 1 / 2) (t : ℝ) :
    actualJMellinIntegral s t = jImaginaryGammaRatio s t := by
  rw [actualJMellinIntegral_eq_gamma_product hs0 hsHalf t,
    poissonGammaValue_eq_jImaginaryGammaRatio hs0 (by linarith : s.re < 1) t]

end
end ImbalancedChen.Part3.ActualJFixedOrderMellinGamma20261026b
