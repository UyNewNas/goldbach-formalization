import ImbalancedChen.Part3JMellinGammaRemovable
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

Real-axis conjugation identifies the prospective J Gamma multiplier with
an exact real Gamma norm square. It is strictly positive for 0<sigma<1,
including the actual Gamma-product extension at t=0. The line sigma=1
has zero multiplier. This fixes the sign implied by the native i times
opposite-order difference rather than choosing that sign by convention.

Actual J Mellin integral -> Gamma ratio remains OPEN. No held convergence
source or actual-transform identification is an input.
-/

namespace ImbalancedChen.Part3.JMellinGammaRealSign20261026b

noncomputable section
open Complex Set
open JMellinGammaParity20261026b JMellinGammaRemovable20261026b

def jRealGammaMultiplier (sigma t : ℝ) : ℝ :=
  (2 : ℝ) ^ sigma / Real.pi * Real.cos (Real.pi * sigma / 2) *
    ‖Gamma ((sigma : ℂ) / 2 + I * (t : ℂ))‖ ^ 2

/-- Literal conjugate pair with t unscaled; the two arguments are exactly
the s/2 +/- it shifts supplied by orders +/-2it. -/
theorem gamma_real_order_conjugate (sigma t : ℝ) :
    Gamma ((sigma : ℂ) / 2 - I * (t : ℂ)) =
      conj (Gamma ((sigma : ℂ) / 2 + I * (t : ℂ))) := by
  rw [← Complex.Gamma_conj]
  congr 1
  simp [sub_eq_add_neg]

theorem jGammaMultiplier_real_norm_sq (sigma t : ℝ) :
    jGammaMultiplier (sigma : ℂ) t = (jRealGammaMultiplier sigma t : ℂ) := by
  have hpow : (2 : ℂ) ^ (sigma : ℂ) = (((2 : ℝ) ^ sigma : ℝ) : ℂ) := by
    exact (Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 2) sigma).symm
  have hcos : Complex.cos ((Real.pi : ℂ) * (sigma : ℂ) / 2) =
      (Real.cos (Real.pi * sigma / 2) : ℂ) := by
    rw [show (Real.pi : ℂ) * (sigma : ℂ) / 2 =
      ((Real.pi * sigma / 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cos]
  rw [jGammaMultiplier, gamma_real_order_conjugate, mul_assoc, Complex.mul_conj', hpow, hcos]
  simp only [jRealGammaMultiplier, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_pow, Complex.ofReal_ofNat]

theorem jGammaMultiplier_real_im_zero (sigma t : ℝ) :
    (jGammaMultiplier (sigma : ℂ) t).im = 0 := by
  rw [jGammaMultiplier_real_norm_sq]
  exact Complex.ofReal_im _

/-- Strict positivity includes t=0, because the Gamma factor has positive
real part in its argument and is therefore genuinely nonzero. -/
theorem jRealGammaMultiplier_pos {sigma : ℝ} (hs0 : 0 < sigma) (hs1 : sigma < 1)
    (t : ℝ) : 0 < jRealGammaMultiplier sigma t := by
  have hang : 0 < Real.pi * sigma / 2 := by positivity
  have hc : 0 < Real.cos (Real.pi * sigma / 2) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · linarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
  have hg : Gamma ((sigma : ℂ) / 2 + I * (t : ℂ)) ≠ 0 := by
    apply Gamma_ne_zero_of_re_pos
    simpa using (show 0 < sigma / 2 by linarith)
  have hn : 0 < ‖Gamma ((sigma : ℂ) / 2 + I * (t : ℂ))‖ := norm_pos_iff.mpr hg
  unfold jRealGammaMultiplier
  exact mul_pos
    (mul_pos (div_pos (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) sigma)
      Real.pi_pos) hc) (sq_pos_of_pos hn)

theorem jGammaMultiplier_re_pos {sigma : ℝ} (hs0 : 0 < sigma) (hs1 : sigma < 1)
    (t : ℝ) : 0 < (jGammaMultiplier (sigma : ℂ) t).re := by
  rw [jGammaMultiplier_real_norm_sq, Complex.ofReal_re]
  exact jRealGammaMultiplier_pos hs0 hs1 t

theorem jGammaMultiplier_one (t : ℝ) : jGammaMultiplier 1 t = 0 := by
  simp [jGammaMultiplier]

end
end ImbalancedChen.Part3.JMellinGammaRealSign20261026b
