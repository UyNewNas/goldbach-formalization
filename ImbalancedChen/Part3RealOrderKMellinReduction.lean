import ImbalancedChen.Part3RealOrderKExceptional
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
CODE_ONLY / SOURCEONLY / UNCOMPILED, 2026-10-25. No acceptance credit.

For every real order alpha and real Mellin exponent s > |alpha|, the
literal realOrderK integral has an absolutely integrable Mellin moment.
Fubini reduces it exactly to Gamma(s) times the cosh-power integral.
The q fiber uses the same pinned Gamma--Laplace theorem as the earlier
actual-K-zero Mellin fiber. The new content is the full convergence strip,
an explicit outer exponential envelope, product integrability and exchange.

The globally measurable auxiliary fiber uses exp(log(q)*(s-1)); its
equality to the actual q^(s-1) kernel on q>0 is proved explicitly. The
final results concern the literal actual realOrderK function.

The Beta substitution evaluating the remaining cosh integral and the
resulting Gamma-product normalization remain OPEN.
-/

namespace ImbalancedChen.Part3.RealOrderKMellinReduction20261025a

noncomputable section
open Set MeasureTheory Filter
open RealOrderKExceptionalSourceOnly

/-- The unevaluated outer integral density for actual K Mellin moments. -/
def mellinDensity (α s u : ℝ) : ℝ :=
  Real.cosh (α * u) * (1 / Real.cosh u) ^ s

private def mellinFiber (α s u q : ℝ) : ℝ :=
  (Real.exp (Real.log q * (s - 1)) * Real.exp (-(Real.cosh u * q))) *
    Real.cosh (α * u)

private theorem mellinFiber_eq_actual (α s u : ℝ) {q : ℝ} (hq : 0 < q) :
    mellinFiber α s u q = q ^ (s - 1) * realOrderIntegrand α q u := by
  dsimp only [mellinFiber, realOrderIntegrand]
  rw [Real.rpow_def_of_pos hq, mul_comm (Real.cosh u) q]
  ring

private theorem mellinFiber_nonneg (α s u q : ℝ) :
    0 ≤ mellinFiber α s u q := by
  unfold mellinFiber
  positivity

private theorem mellinFiber_integrable (α s u : ℝ) (hs : 0 < s) :
    IntegrableOn (mellinFiber α s u) (Ioi (0 : ℝ)) := by
  have hbase : IntegrableOn
      (fun q : ℝ => q ^ (s - 1) * Real.exp (-(Real.cosh u * q))) (Ioi 0) := by
    simpa only [Real.rpow_one, neg_mul] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (p := (1 : ℝ)) (s := s - 1) (b := Real.cosh u)
        (by linarith) le_rfl (Real.cosh_pos u))
  apply (hbase.mul_const (Real.cosh (α * u))).congr_fun _ measurableSet_Ioi
  intro q hq
  dsimp only [mellinFiber]
  rw [Real.rpow_def_of_pos hq]

private theorem mellinFiber_q_integral (α s u : ℝ) (hs : 0 < s) :
    (∫ q in Ioi (0 : ℝ), mellinFiber α s u q) =
      Real.Gamma s * mellinDensity α s u := by
  calc
    (∫ q in Ioi (0 : ℝ), mellinFiber α s u q) =
      ∫ q in Ioi (0 : ℝ),
        (q ^ (s - 1) * Real.exp (-(Real.cosh u * q))) * Real.cosh (α * u) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
      dsimp only [mellinFiber]
      rw [Real.rpow_def_of_pos hq]
    _ = ((1 / Real.cosh u) ^ s * Real.Gamma s) * Real.cosh (α * u) := by
      rw [integral_mul_const,
        Real.integral_rpow_mul_exp_neg_mul_Ioi hs (Real.cosh_pos u)]
    _ = Real.Gamma s * mellinDensity α s u := by
      dsimp only [mellinDensity]
      ring

theorem mellinDensity_nonneg (α s u : ℝ) : 0 ≤ mellinDensity α s u := by
  exact mul_nonneg (Real.cosh_pos _).le
    (Real.rpow_nonneg (one_div_nonneg.mpr (Real.cosh_pos u).le) s)

private theorem cosh_order_le_exp_abs (α : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    Real.cosh (α * u) ≤ Real.exp (|α| * u) := by
  have hp : Real.exp (α * u) ≤ Real.exp (|α| * u) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_abs_self α) hu)
  have hn : Real.exp (-(α * u)) ≤ Real.exp (|α| * u) := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_right (neg_le_abs α) hu
    nlinarith
  rw [Real.cosh_eq]
  linarith

private theorem sech_le_exp (u : ℝ) :
    1 / Real.cosh u ≤ 2 * Real.exp (-u) := by
  have hc := Real.cosh_pos u
  have hexp : Real.exp u * Real.exp (-u) = 1 := by
    rw [← Real.exp_add]
    simp
  apply (div_le_iff₀ hc).2
  rw [Real.cosh_eq]
  nlinarith [sq_nonneg (Real.exp (-u))]

/-- The exact Mellin convergence gap s-|alpha| appears in an elementary
integrable exponential envelope. No K/Mellin estimate is a premise. -/
theorem mellinDensity_le_exp {α s u : ℝ} (hs : |α| < s) (hu : 0 ≤ u) :
    mellinDensity α s u ≤
      (2 : ℝ) ^ s * Real.exp (-(s - |α|) * u) := by
  have hs0 : 0 < s := lt_of_le_of_lt (abs_nonneg α) hs
  have hpow : (1 / Real.cosh u) ^ s ≤
      (2 : ℝ) ^ s * Real.exp ((-u) * s) := by
    calc
      (1 / Real.cosh u) ^ s ≤ (2 * Real.exp (-u)) ^ s :=
        Real.rpow_le_rpow (by positivity) (sech_le_exp u) hs0.le
      _ = (2 : ℝ) ^ s * Real.exp ((-u) * s) := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Real.exp_pos _).le,
          ← Real.exp_mul]
  calc
    mellinDensity α s u ≤
        Real.exp (|α| * u) * ((2 : ℝ) ^ s * Real.exp ((-u) * s)) :=
      mul_le_mul (cosh_order_le_exp_abs α hu) hpow
        (by positivity) (Real.exp_pos _).le
    _ = (2 : ℝ) ^ s *
        (Real.exp (|α| * u) * Real.exp ((-u) * s)) := by ring
    _ = (2 : ℝ) ^ s * Real.exp (-(s - |α|) * u) := by
      rw [← Real.exp_add]
      congr 2
      ring

private theorem mellinEnvelope_integrable {α s : ℝ} (hs : |α| < s) :
    IntegrableOn (fun u : ℝ =>
      (2 : ℝ) ^ s * Real.exp (-(s - |α|) * u)) (Ioi 0) := by
  exact (integrableOn_exp_mul_Ioi (by linarith : -(s - |α|) < 0) 0).const_mul _

theorem mellinDensity_integrable {α s : ℝ} (hs : |α| < s) :
    IntegrableOn (mellinDensity α s) (Ioi (0 : ℝ)) := by
  have hs0 : 0 < s := lt_of_le_of_lt (abs_nonneg α) hs
  have hc : Continuous (mellinDensity α s) := by
    have hcosh : Continuous (fun u : ℝ => Real.cosh (α * u)) := by fun_prop
    have hsech : Continuous (fun u : ℝ => 1 / Real.cosh u) := by
      fun_prop (disch := positivity)
    exact hcosh.mul ((Real.continuous_rpow_const hs0.le).comp hsech)
  apply (mellinEnvelope_integrable hs).mono' hc.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [Real.norm_eq_abs, abs_of_nonneg (mellinDensity_nonneg α s u)]
  exact mellinDensity_le_exp hs hu.le

private theorem mellinFiber_joint_integrable {α s : ℝ} (hs : |α| < s) :
    Integrable (fun p : ℝ × ℝ => mellinFiber α s p.1 p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod
        (volume.restrict (Ioi (0 : ℝ)))) := by
  have hs0 : 0 < s := lt_of_le_of_lt (abs_nonneg α) hs
  have hm : Measurable (fun p : ℝ × ℝ => mellinFiber α s p.1 p.2) := by
    unfold mellinFiber
    fun_prop
  apply (integrable_prod_iff hm.aestronglyMeasurable).2
  constructor
  · exact ae_of_all _ (fun u => mellinFiber_integrable α s u hs0)
  · have he : (fun u : ℝ => ∫ q in Ioi (0 : ℝ), ‖mellinFiber α s u q‖) =
        fun u : ℝ => Real.Gamma s * mellinDensity α s u := by
      funext u
      rw [← mellinFiber_q_integral α s u hs0]
      apply integral_congr_ae
      exact ae_of_all _ (fun q => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mellinFiber_nonneg α s u q)])
    simpa only [he] using (mellinDensity_integrable hs).const_mul (Real.Gamma s)

private theorem mellinFiber_u_integral (α s : ℝ) {q : ℝ} (hq : 0 < q) :
    (∫ u in Ioi (0 : ℝ), mellinFiber α s u q) =
      q ^ (s - 1) * realOrderK α q := by
  change (∫ u in Ioi (0 : ℝ), mellinFiber α s u q) =
    q ^ (s - 1) * ∫ u in Ioi (0 : ℝ), realOrderIntegrand α q u
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun u => mellinFiber_eq_actual α s u hq)

/-- Full real Mellin convergence strip for the literal actual real-order K
integral. It includes exceptional orders but is not restricted to them. -/
theorem realOrderK_mellin_integrable {α s : ℝ} (hs : |α| < s) :
    IntegrableOn (fun q : ℝ => q ^ (s - 1) * realOrderK α q) (Ioi 0) := by
  have h := (mellinFiber_joint_integrable hs).integral_prod_right
  apply h.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
  exact mellinFiber_u_integral α s hq

/-- Exact actual-K Mellin reduction, with a proved product-integrability
certificate. The unevaluated cosh integral is explicit in the conclusion. -/
theorem realOrderK_mellin_reduction {α s : ℝ} (hs : |α| < s) :
    (∫ q in Ioi (0 : ℝ), q ^ (s - 1) * realOrderK α q) =
      Real.Gamma s * ∫ u in Ioi (0 : ℝ), mellinDensity α s u := by
  have hs0 : 0 < s := lt_of_le_of_lt (abs_nonneg α) hs
  calc
    (∫ q in Ioi (0 : ℝ), q ^ (s - 1) * realOrderK α q) =
        ∫ q in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ), mellinFiber α s u q := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
      exact (mellinFiber_u_integral α s hq).symm
    _ = ∫ u in Ioi (0 : ℝ), ∫ q in Ioi (0 : ℝ), mellinFiber α s u q :=
      (integral_integral_swap (mellinFiber_joint_integrable hs)).symm
    _ = Real.Gamma s * ∫ u in Ioi (0 : ℝ), mellinDensity α s u := by
      simp only [mellinFiber_q_integral α s _ hs0, integral_const_mul]

end
end ImbalancedChen.Part3.RealOrderKMellinReduction20261025a
