import ImbalancedChen.Part3RealOrderKMellinReduction
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

/-!
CODE_ONLY / SOURCEONLY / UNCOMPILED, 2026-10-25. No acceptance credit.

One concrete substitution step toward actual real-order K Mellin
normalization: t = exp(2u) converts the convergent cosh-power integral
to the explicit paired Euler kernel on t>1. Integrability of that actual
kernel is transported from the proved Mellin convergence strip.

Pinned Mathlib Gamma/Beta provides Complex.betaIntegral on [0,1] and
Gamma_mul_Gamma_eq_betaIntegral. It does not directly identify this paired
half-line kernel. Reciprocal-tail gluing and the remaining Euler compact
substitution remain OPEN; no Beta evaluation is assumed.
-/

namespace ImbalancedChen.Part3.RealOrderKMellinBetaTail20261025a

noncomputable section
open Set MeasureTheory
open RealOrderKExceptionalSourceOnly
open RealOrderKMellinReduction20261025a

/-- Paired Euler half-line powers after t=exp(2u). -/
def betaTailDensity (α s t : ℝ) : ℝ :=
  (t ^ ((s + α) / 2 - 1) + t ^ ((s - α) / 2 - 1)) / (1 + t) ^ s

private def expTailProfile (α s x : ℝ) : ℝ :=
  Real.exp x * betaTailDensity α s (Real.exp x)

private theorem inverse_cosh_eq_exp (u : ℝ) :
    1 / Real.cosh u = 2 * Real.exp u / (1 + Real.exp (2 * u)) := by
  have hprod : Real.exp u * Real.exp (-u) = 1 := by
    rw [← Real.exp_add]
    simp
  have hdouble : Real.exp (2 * u) = Real.exp u * Real.exp u := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hden : 1 + Real.exp (2 * u) = 2 * Real.exp u * Real.cosh u := by
    rw [Real.cosh_eq]
    nlinarith
  rw [hden]
  field_simp [(Real.exp_pos u).ne', (Real.cosh_pos u).ne'] <;> ring

/-- Literal pullback identity, including the factor lost by u↦exp(2u).
This is an algebraic identity for every real alpha,s,u. -/
theorem mellinDensity_eq_expTailProfile (α s u : ℝ) :
    mellinDensity α s u = (2 : ℝ) ^ s / 2 * expTailProfile α s (2 * u) := by
  have hpow : (1 / Real.cosh u) ^ s =
      (2 : ℝ) ^ s * Real.exp (u * s) / (1 + Real.exp (2 * u)) ^ s := by
    rw [inverse_cosh_eq_exp,
      Real.div_rpow (by positivity) (by positivity) s,
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Real.exp_pos u).le,
      ← Real.exp_mul]
  have hp : Real.exp (2 * u) *
      (Real.exp (2 * u)) ^ ((s + α) / 2 - 1) =
        Real.exp (u * s) * Real.exp (α * u) := by
    rw [← Real.exp_mul, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hn : Real.exp (2 * u) *
      (Real.exp (2 * u)) ^ ((s - α) / 2 - 1) =
        Real.exp (u * s) * Real.exp (-(α * u)) := by
    rw [← Real.exp_mul, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hsum : Real.exp (2 * u) *
      ((Real.exp (2 * u)) ^ ((s + α) / 2 - 1) +
        (Real.exp (2 * u)) ^ ((s - α) / 2 - 1)) =
      Real.exp (u * s) * (Real.exp (α * u) + Real.exp (-(α * u))) := by
    rw [mul_add, hp, hn]
    ring
  calc
    mellinDensity α s u =
        (Real.exp (α * u) + Real.exp (-(α * u))) / 2 *
          ((2 : ℝ) ^ s * Real.exp (u * s) /
            (1 + Real.exp (2 * u)) ^ s) := by
      rw [mellinDensity, Real.cosh_eq, hpow]
    _ = (2 : ℝ) ^ s / 2 *
        (Real.exp (u * s) * (Real.exp (α * u) + Real.exp (-(α * u))) /
          (1 + Real.exp (2 * u)) ^ s) := by ring
    _ = (2 : ℝ) ^ s / 2 *
        (Real.exp (2 * u) *
          ((Real.exp (2 * u)) ^ ((s + α) / 2 - 1) +
            (Real.exp (2 * u)) ^ ((s - α) / 2 - 1)) /
          (1 + Real.exp (2 * u)) ^ s) := by rw [hsum]
    _ = (2 : ℝ) ^ s / 2 * expTailProfile α s (2 * u) := by
      dsimp only [expTailProfile, betaTailDensity]
      ring

private theorem expTailProfile_integrable {α s : ℝ} (hs : |α| < s) :
    IntegrableOn (expTailProfile α s) (Ioi (0 : ℝ)) := by
  have hcoef : (2 : ℝ) ^ s / 2 ≠ 0 := by positivity
  have hscaled : IntegrableOn (fun u : ℝ => expTailProfile α s (2 * u)) (Ioi 0) := by
    apply ((mellinDensity_integrable hs).div_const ((2 : ℝ) ^ s / 2)).congr_fun
      _ measurableSet_Ioi
    intro u _
    rw [mellinDensity_eq_expTailProfile]
    exact mul_div_cancel_left₀ _ hcoef
  have h := (integrableOn_Ioi_comp_mul_left_iff (expTailProfile α s) 0
    (a := (2 : ℝ)) (by norm_num)).mp hscaled
  simpa only [mul_zero] using h

/-- The explicit Euler tail kernel is absolutely integrable on t>1
throughout the full actual-K real Mellin convergence strip. -/
theorem betaTailDensity_integrable {α s : ℝ} (hs : |α| < s) :
    IntegrableOn (betaTailDensity α s) (Ioi (1 : ℝ)) := by
  have h := (integrableOn_comp_exp_Ioi (betaTailDensity α s) 0).mp
    (by simpa only [expTailProfile, smul_eq_mul] using expTailProfile_integrable hs)
  simpa only [Real.exp_zero] using h

/-- The exact t=exp(2u) substitution for the actual cosh-power integral.
The coefficient 2^s/4 accounts for both cosh and the Jacobian. -/
theorem mellinDensity_integral_eq_betaTail (α s : ℝ) :
    (∫ u in Ioi (0 : ℝ), mellinDensity α s u) =
      (2 : ℝ) ^ s / 4 * ∫ t in Ioi (1 : ℝ), betaTailDensity α s t := by
  have hexp : (∫ x in Ioi (0 : ℝ), expTailProfile α s x) =
      ∫ t in Ioi (1 : ℝ), betaTailDensity α s t := by
    simpa only [expTailProfile, smul_eq_mul, Real.exp_zero] using
      integral_comp_exp_Ioi (betaTailDensity α s) 0
  have hscale : (∫ u in Ioi (0 : ℝ), expTailProfile α s (2 * u)) =
      (1 / 2 : ℝ) * ∫ x in Ioi (0 : ℝ), expTailProfile α s x := by
    simpa only [mul_zero, smul_eq_mul, inv_eq_one_div] using
      integral_comp_mul_left_Ioi (expTailProfile α s) 0
        (b := (2 : ℝ)) (by norm_num)
  calc
    (∫ u in Ioi (0 : ℝ), mellinDensity α s u) =
        (2 : ℝ) ^ s / 2 * ∫ u in Ioi (0 : ℝ), expTailProfile α s (2 * u) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (mellinDensity_eq_expTailProfile α s)
    _ = (2 : ℝ) ^ s / 4 * ∫ t in Ioi (1 : ℝ), betaTailDensity α s t := by
      rw [hscale, hexp]
      ring

/-- The literal actual K Mellin moment after this concrete Euler-tail step. -/
theorem realOrderK_mellin_eq_betaTail {α s : ℝ} (hs : |α| < s) :
    (∫ q in Ioi (0 : ℝ), q ^ (s - 1) * realOrderK α q) =
      (Real.Gamma s * (2 : ℝ) ^ s / 4) *
        ∫ t in Ioi (1 : ℝ), betaTailDensity α s t := by
  rw [realOrderK_mellin_reduction hs, mellinDensity_integral_eq_betaTail]
  ring

end
end ImbalancedChen.Part3.RealOrderKMellinBetaTail20261025a
