import ImbalancedChen.Part3JMellinGammaParity

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

The prospective J Gamma multiplier has a genuine continuous removable
order-zero value. Its punctured quotient limit is derived from actual
Gamma continuity and the reflection identity, with the exact native i,
pi, and two-order factors. This file neither proves nor assumes an actual
J Mellin integral equals a Gamma ratio. No held convergence chain is used.
-/

namespace ImbalancedChen.Part3.JMellinGammaRemovable20261026b

noncomputable section
open Complex Set Filter
open scoped Topology
open JMellinGammaParity20261026b

private theorem Gamma_continuousAt_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    ContinuousAt Gamma z := by
  apply Complex.continuousAt_Gamma
  intro n hn
  have he := congrArg Complex.re hn
  simp only [Complex.neg_re, Complex.natCast_re] at he
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

/-- Continuity is proved from the actual Gamma function; there is no
continuity assumption on a multiplier or on a formal Mellin transform. -/
theorem jGammaMultiplier_continuous {s : ℂ} (hs : 0 < s.re) :
    Continuous (jGammaMultiplier s) := by
  have hp : Continuous (fun t : ℝ => Gamma (s / 2 + I * (t : ℂ))) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hre : 0 < (s / 2 + I * (t : ℂ)).re := by
      simpa using (show 0 < s.re / 2 by linarith)
    exact (Gamma_continuousAt_of_re_pos hre).comp (by fun_prop)
  have hn : Continuous (fun t : ℝ => Gamma (s / 2 - I * (t : ℂ))) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hre : 0 < (s / 2 - I * (t : ℂ)).re := by
      simpa using (show 0 < s.re / 2 by linarith)
    exact (Gamma_continuousAt_of_re_pos hre).comp (by fun_prop)
  exact (continuous_const.mul hp).mul hn

theorem jGammaMultiplier_even (s : ℂ) (t : ℝ) :
    jGammaMultiplier s (-t) = jGammaMultiplier s t := by
  simp only [jGammaMultiplier, Complex.ofReal_neg, mul_neg, sub_neg_eq_add]
  ring

/-- Exact removable value, including the constant from i times the
difference of the two opposite orders. -/
theorem jGammaMultiplier_zero (s : ℂ) :
    jGammaMultiplier s 0 =
      (2 : ℂ) ^ s / (Real.pi : ℂ) * Complex.cos ((Real.pi : ℂ) * s / 2) *
        Gamma (s / 2) ^ 2 := by
  simp [jGammaMultiplier, pow_two, mul_assoc]

theorem jGammaRatio_quotient_tendsto_zero {s : ℂ}
    (hs0 : 0 < s.re) (hs2 : s.re < 2) :
    Tendsto (fun t : ℝ =>
      I * (jImaginaryGammaRatio s t - jImaginaryGammaRatio s (-t)) /
        (Real.sinh (Real.pi * t) : ℂ)) (𝓝[≠] 0)
      (𝓝 ((2 : ℂ) ^ s / (Real.pi : ℂ) *
        Complex.cos ((Real.pi : ℂ) * s / 2) * Gamma (s / 2) ^ 2)) := by
  have h := (jGammaMultiplier_continuous hs0).continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds : (𝓝[≠] (0 : ℝ)) ≤ 𝓝 0)
  rw [jGammaMultiplier_zero] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact jGammaRatio_quotient_eq hs0 hs2 ht

/-- The raw field quotient is zero at the origin; it must not be used
there in place of the genuine Gamma-product extension above. -/
theorem jGammaRatio_raw_quotient_zero (s : ℂ) :
    I * (jImaginaryGammaRatio s 0 - jImaginaryGammaRatio s (-0)) /
      (Real.sinh (Real.pi * 0) : ℂ) = 0 := by simp

end
end ImbalancedChen.Part3.JMellinGammaRemovable20261026b
