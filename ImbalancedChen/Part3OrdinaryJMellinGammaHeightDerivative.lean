import ImbalancedChen.Part3OrdinaryJMellinHeightDerivative
import ImbalancedChen.Part3ActualJFixedOrderMellinGamma

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

Standalone ordinary-J parameter Mellin derivative evaluated by the native
derivative of the canonical Gamma ratio. Actual derivative Mellin L1 and
interchange are proved in the imported ordinary module. Actual fixed-order
Mellin/Gamma identification is proved independently in its integral chain.
No critical kernel, derivative-interchange, or domination premise is used.
-/

namespace ImbalancedChen.Part3.OrdinaryJMellinGammaHeightDerivative20261026b

noncomputable section
open Complex Filter Set MeasureTheory
open scoped Topology
open JMellinGammaParity20261026b ActualJFixedOrderMellinL120261026b
open ActualJFixedOrderMellinGamma20261026b OrdinaryJHeightMellinNearZero20261026b
open OrdinaryJMellinHeightDerivative20261026b

def jImaginaryGammaRatioHeightDerivative (s : ℂ) (t : ℝ) : ℂ :=
  (2 : ℂ) ^ (s - 1) * I *
    (deriv Gamma (s / 2 + I * (t : ℂ)) * Gamma (1 - s / 2 + I * (t : ℂ)) -
      Gamma (s / 2 + I * (t : ℂ)) * deriv Gamma (1 - s / 2 + I * (t : ℂ))) /
        Gamma (1 - s / 2 + I * (t : ℂ)) ^ 2

private theorem Gamma_hasDerivAt_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt Gamma (deriv Gamma z) z := by
  apply DifferentiableAt.hasDerivAt
  apply Complex.differentiableAt_Gamma
  intro n hn
  have he := congrArg Complex.re hn
  simp only [Complex.neg_re, Complex.natCast_re] at he
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

/-- Native real-height derivative of the canonical ordinary-J Gamma ratio. -/
theorem jImaginaryGammaRatio_height_hasDerivAt {s : ℂ}
    (hs0 : 0 < s.re) (hs2 : s.re < 2) (t : ℝ) :
    HasDerivAt (jImaginaryGammaRatio s) (jImaginaryGammaRatioHeightDerivative s t) t := by
  have ha : 0 < (s / 2 + I * (t : ℂ)).re := by simpa using (show 0 < s.re / 2 by linarith)
  have hb : 0 < (1 - s / 2 + I * (t : ℂ)).re := by simpa using (show 0 < 1 - s.re / 2 by linarith)
  have hpA : HasDerivAt (fun z : ℂ => s / 2 + I * z) I (t : ℂ) :=
    ((hasDerivAt_id (t : ℂ)).const_mul I).const_add (s / 2)
  have hpB : HasDerivAt (fun z : ℂ => 1 - s / 2 + I * z) I (t : ℂ) :=
    ((hasDerivAt_id (t : ℂ)).const_mul I).const_add (1 - s / 2)
  have hA := ((Gamma_hasDerivAt_of_re_pos ha).comp (t : ℂ) hpA).comp_ofReal
  have hB := ((Gamma_hasDerivAt_of_re_pos hb).comp (t : ℂ) hpB).comp_ofReal
  have h := (hA.div hB (Gamma_ne_zero_of_re_pos hb)).const_mul ((2 : ℂ) ^ (s - 1))
  convert h using 1
  · funext x
    unfold jImaginaryGammaRatio
    ring
  · unfold jImaginaryGammaRatioHeightDerivative
    ring

/-- Evaluated genuine ordinary-J derivative Mellin integral, including
the ordinary single-J order derivative at t=0. No critical quotient is
defined or combined in this theorem. -/
theorem ordinaryJHeightMellinIntegral_eq_GammaDerivative {s : ℂ}
    (hs0 : 0 < s.re) (hsHalf : s.re < 1 / 2) (t : ℝ) :
    (∫ q in Ioi (0 : ℝ), ordinaryJHeightMellinIntegrand s t q) =
      jImaginaryGammaRatioHeightDerivative s t := by
  have he : actualJMellinIntegral s =ᶠ[𝓝 t] jImaginaryGammaRatio s :=
    Eventually.of_forall (fun x => actualJMellinIntegral_eq_gamma_ratio hs0 hsHalf x)
  exact (actualJMellinIntegral_height_hasDerivAt hs0 hsHalf t).unique
    ((jImaginaryGammaRatio_height_hasDerivAt hs0 (by linarith : s.re < 2) t)
      .congr_of_eventuallyEq he)

theorem actualJMellinIntegral_height_deriv_eq_GammaDerivative {s : ℂ}
    (hs0 : 0 < s.re) (hsHalf : s.re < 1 / 2) (t : ℝ) :
    deriv (actualJMellinIntegral s) t = jImaginaryGammaRatioHeightDerivative s t := by
  rw [(actualJMellinIntegral_height_hasDerivAt hs0 hsHalf t).deriv,
    ordinaryJHeightMellinIntegral_eq_GammaDerivative hs0 hsHalf t]

end
end ImbalancedChen.Part3.OrdinaryJMellinGammaHeightDerivative20261026b
