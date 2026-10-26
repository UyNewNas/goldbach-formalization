import ImbalancedChen.Part3ActualRealOrderJAngularGamma
import ImbalancedChen.Part3ActualJFixedOrderMellinGamma

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

Actual real-order J Mellin dictionary, including the complementary orders
nu=+/-7/16. The actual full integral is already evaluated to a Gamma
product; the proved general complex cosine/Gamma duplication-reflection
identity now reduces it to the canonical general-order ratio.

This is an Archimedean special-function identity only. Full Kuznetsov,
exceptional spectral completeness, the 7/32 theorem, and the original
automorphic overall normalization remain OPEN.
-/

namespace ImbalancedChen.Part3.ActualRealOrderJMellinGamma20261026b

noncomputable section
open Complex
open JMellinGammaParity20261026b ActualJFixedOrderMellinGamma20261026b
open ActualRealOrderJMellinL120261026b ActualRealOrderJAbelPoisson20261026b
open ActualRealOrderJAngularGamma20261026b

theorem realPoissonGammaValue_eq_jGammaRatio {s : ℂ} {nu : ℝ}
    (hn : -(1 / 2 : ℝ) < nu) (ha0 : 0 < s.re + nu) (ha1 : s.re + nu < 1) :
    realPoissonMellinConstant nu * realAngularGammaValue s nu = jGammaRatio s (nu : ℂ) := by
  let a : ℂ := s + (nu : ℂ)
  have hre : a.re = s.re + nu := by dsimp [a]; simp
  have hprod := cosine_Gamma_half_product (a := a)
    (by rw [hre]; exact ha0) (by rw [hre]; exact ha1)
  have hS : (Real.sqrt Real.pi : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 Real.pi_pos).ne'
  have hNu : 0 < ((nu : ℂ) + 1 / 2).re := by simpa using (show 0 < nu + 1 / 2 by linarith)
  have hGnu : Gamma ((nu : ℂ) + 1 / 2) ≠ 0 := Gamma_ne_zero_of_re_pos hNu
  have hAlpha : 0 < ((1 - a) / 2).re := by
    simpa using (show 0 < (1 - a.re) / 2 by rw [hre]; linarith)
  have hGden : Gamma ((1 - a) / 2 + (nu : ℂ) + 1 / 2) ≠ 0 := by
    apply Gamma_ne_zero_of_re_pos
    rw [show (1 - a) / 2 + (nu : ℂ) + 1 / 2 = (1 - a) / 2 + ((nu : ℂ) + 1 / 2) by ring,
      Complex.add_re]
    exact add_pos hAlpha hNu
  have hden : (1 - a) / 2 + (nu : ℂ) + 1 / 2 = (2 - s + (nu : ℂ)) / 2 := by dsimp [a]; ring
  have hp : (2 : ℂ) ^ (-(nu : ℂ)) * (2 : ℂ) ^ (a - 1) = (2 : ℂ) ^ (s - 1) := by
    rw [← Complex.cpow_add (-(nu : ℂ)) (a - 1) (by norm_num : (2 : ℂ) ≠ 0)]
    congr 1
    dsimp [a]
    ring
  change ((2 : ℂ) ^ (-(nu : ℂ)) / ((Real.sqrt Real.pi : ℂ) * Gamma ((nu : ℂ) + 1 / 2))) *
      ((Complex.cos ((Real.pi : ℂ) * a / 2) * Gamma a * Gamma ((1 - a) / 2)) *
        Gamma ((nu : ℂ) + 1 / 2) / Gamma ((1 - a) / 2 + (nu : ℂ) + 1 / 2)) = _
  rw [hprod]
  calc
    _ = ((2 : ℂ) ^ (-(nu : ℂ)) * (2 : ℂ) ^ (a - 1)) * Gamma (a / 2) /
        Gamma ((1 - a) / 2 + (nu : ℂ) + 1 / 2) := by
      field_simp [hS, hGnu, hGden] <;> ring
    _ = jGammaRatio s (nu : ℂ) := by
      rw [hp, hden]
      rfl

/-- The actual real complementary-order J Mellin integral equals the
canonical Gamma ratio on its genuine absolute-convergence strip. -/
theorem realOrderJMellinIntegral_eq_gamma_ratio {s : ℂ} {nu : ℝ}
    (hnu : |nu| < 1 / 2) (hsnu : 0 < s.re + nu) (hsHalf : s.re < 1 / 2) :
    realOrderJMellinIntegral s nu = jGammaRatio s (nu : ℂ) := by
  have hn := abs_lt.mp hnu
  rw [realOrderJMellinIntegral_eq_gamma_product hnu hsnu hsHalf,
    realPoissonGammaValue_eq_jGammaRatio hn.1 hsnu (by linarith [hn.2] : s.re + nu < 1)]

theorem realOrderJMellinIntegral_eq_literal_gamma {s : ℂ} {nu : ℝ}
    (hnu : |nu| < 1 / 2) (hsnu : 0 < s.re + nu) (hsHalf : s.re < 1 / 2) :
    realOrderJMellinIntegral s nu =
      (2 : ℂ) ^ (s - 1) * Gamma ((s + (nu : ℂ)) / 2) /
        Gamma (1 + ((nu : ℂ) - s) / 2) := by
  rw [realOrderJMellinIntegral_eq_gamma_ratio hnu hsnu hsHalf]
  unfold jGammaRatio
  rw [show (2 - s + (nu : ℂ)) / 2 = 1 + ((nu : ℂ) - s) / 2 by ring]

end
end ImbalancedChen.Part3.ActualRealOrderJMellinGamma20261026b
