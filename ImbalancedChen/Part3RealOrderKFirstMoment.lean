import ImbalancedChen.Part3RealOrderKExceptional
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
CODE_ONLY / SOURCEONLY / UNCOMPILED, 2026-10-25. No acceptance credit.

The literal real-order K integral now has a proved integrable first q
moment, with the variables exchanged and its exact cosh-density retained.
The proof works for the larger order interval |alpha| <= 1; in particular
it includes every exceptional order |alpha| <= 7/32. Neither K-moment
integrability nor a Mellin/Fubini formula is an input.

This is a normalization reduction, not the Gamma-product evaluation.
The remaining integral has not been replaced by an assumed Beta formula.
No automorphic spectral measure or Kuznetsov normalization is asserted.
-/

namespace ImbalancedChen.Part3.RealOrderKFirstMoment20261025a

noncomputable section
open Set MeasureTheory Filter
open RealOrderKExceptionalSourceOnly

/-- The exact density left after integrating the actual K kernel in q. -/
def firstMomentDensity (α u : ℝ) : ℝ :=
  Real.cosh (α * u) * (1 / Real.cosh u) ^ 2

private def momentFiber (α u q : ℝ) : ℝ :=
  (q * Real.exp (-(Real.cosh u * q))) * Real.cosh (α * u)

private theorem momentFiber_nonneg (α u : ℝ) {q : ℝ} (hq : 0 ≤ q) :
    0 ≤ momentFiber α u q := by
  unfold momentFiber
  exact mul_nonneg (mul_nonneg hq (Real.exp_pos _).le) (Real.cosh_pos _).le

/-- This Gamma fiber has no restriction on the real Bessel order. -/
theorem firstMomentDensity_eq_q_integral (α u : ℝ) :
    (∫ q in Ioi (0 : ℝ), momentFiber α u q) =
      firstMomentDensity α u := by
  have hgamma : Real.Gamma (2 : ℝ) = 1 := by
    simpa using Real.Gamma_nat_eq_factorial 1
  have hbase :
      (∫ q in Ioi (0 : ℝ), q * Real.exp (-(Real.cosh u * q))) =
        (1 / Real.cosh u) ^ 2 := by
    simpa [hgamma] using
      (Real.integral_rpow_mul_exp_neg_mul_Ioi
        (a := (2 : ℝ)) (r := Real.cosh u) (by norm_num) (Real.cosh_pos u))
  change (∫ q in Ioi (0 : ℝ),
    (q * Real.exp (-(Real.cosh u * q))) * Real.cosh (α * u)) =
      Real.cosh (α * u) * (1 / Real.cosh u) ^ 2
  rw [integral_mul_const, hbase, mul_comm]

private theorem momentFiber_integrable (α u : ℝ) :
    IntegrableOn (momentFiber α u) (Ioi (0 : ℝ)) := by
  have hbase : IntegrableOn
      (fun q : ℝ => q * Real.exp (-(Real.cosh u * q))) (Ioi 0) := by
    simpa only [Real.rpow_one, neg_mul] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (p := (1 : ℝ)) (s := (1 : ℝ)) (b := Real.cosh u)
        (by norm_num) le_rfl (Real.cosh_pos u))
  exact hbase.mul_const (Real.cosh (α * u))

theorem firstMomentDensity_nonneg (α u : ℝ) :
    0 ≤ firstMomentDensity α u := by
  exact mul_nonneg (Real.cosh_pos _).le (sq_nonneg _)

/-- Order comparison is literal cosh comparison, including negative orders. -/
theorem firstMomentDensity_mono_abs {α β : ℝ} (hαβ : |α| ≤ |β|) (u : ℝ) :
    firstMomentDensity α u ≤ firstMomentDensity β u := by
  have horder : Real.cosh (α * u) ≤ Real.cosh (β * u) := by
    apply Real.cosh_le_cosh.mpr
    simpa only [abs_mul] using mul_le_mul_of_nonneg_right hαβ (abs_nonneg u)
  exact mul_le_mul_of_nonneg_right horder (sq_nonneg _)

/-- An elementary envelope, valid up to real order one. It controls both
the zero end of the q-moment and its infinite tail through Fubini. -/
theorem firstMomentDensity_le_exp {α u : ℝ}
    (hα : |α| ≤ 1) (hu : 0 ≤ u) :
    firstMomentDensity α u ≤ 2 * Real.exp (-u) := by
  have hc : 0 < Real.cosh u := Real.cosh_pos u
  have horder : Real.cosh (α * u) ≤ Real.cosh u := by
    apply Real.cosh_le_cosh.mpr
    rw [abs_mul, abs_of_nonneg hu]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hα hu
  have hdensity : firstMomentDensity α u ≤ 1 / Real.cosh u := by
    calc
      firstMomentDensity α u ≤ Real.cosh u * (1 / Real.cosh u) ^ 2 :=
        mul_le_mul_of_nonneg_right horder (sq_nonneg _)
      _ = 1 / Real.cosh u := by field_simp [hc.ne']; ring
  have hexp : Real.exp u * Real.exp (-u) = 1 := by
    rw [← Real.exp_add]
    simp
  have hsech : 1 / Real.cosh u ≤ 2 * Real.exp (-u) := by
    apply (div_le_iff₀ hc).2
    rw [Real.cosh_eq]
    nlinarith [sq_nonneg (Real.exp (-u))]
  exact hdensity.trans hsech

private theorem expEnvelope_integrable :
    IntegrableOn (fun u : ℝ => 2 * Real.exp (-u)) (Ioi 0) := by
  have h : IntegrableOn (fun u : ℝ => Real.exp ((-1 : ℝ) * u)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (by norm_num) 0
  simpa only [neg_one_mul] using h.const_mul 2

private theorem expEnvelope_integral :
    (∫ u in Ioi (0 : ℝ), 2 * Real.exp (-u)) = 2 := by
  rw [integral_const_mul]
  have h : (∫ u in Ioi (0 : ℝ), Real.exp (-u)) = 1 := by
    simpa using integral_exp_mul_Ioi (a := (-1 : ℝ)) (by norm_num) 0
  rw [h, mul_one]

theorem firstMomentDensity_integrable {α : ℝ} (hα : |α| ≤ 1) :
    IntegrableOn (firstMomentDensity α) (Ioi (0 : ℝ)) := by
  have hc : Continuous (firstMomentDensity α) := by
    unfold firstMomentDensity
    fun_prop (disch := positivity)
  apply expEnvelope_integrable.mono' hc.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [Real.norm_eq_abs, abs_of_nonneg (firstMomentDensity_nonneg α u)]
  exact firstMomentDensity_le_exp hα hu.le

private theorem momentFiber_joint_integrable {α : ℝ} (hα : |α| ≤ 1) :
    Integrable (fun p : ℝ × ℝ => momentFiber α p.1 p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod
        (volume.restrict (Ioi (0 : ℝ)))) := by
  have hc : Continuous (fun p : ℝ × ℝ => momentFiber α p.1 p.2) := by
    unfold momentFiber
    fun_prop
  apply (integrable_prod_iff hc.aestronglyMeasurable).2
  constructor
  · exact ae_of_all _ (fun u => momentFiber_integrable α u)
  · have he : (fun u : ℝ => ∫ q in Ioi (0 : ℝ), ‖momentFiber α u q‖) =
        firstMomentDensity α := by
      funext u
      rw [← firstMomentDensity_eq_q_integral α u]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
      rw [Real.norm_eq_abs, abs_of_nonneg (momentFiber_nonneg α u hq.le)]
    simpa only [he] using firstMomentDensity_integrable hα

private theorem momentFiber_u_integral (α q : ℝ) :
    (∫ u in Ioi (0 : ℝ), momentFiber α u q) = q * realOrderK α q := by
  change (∫ u in Ioi (0 : ℝ), momentFiber α u q) =
    q * ∫ u in Ioi (0 : ℝ), realOrderIntegrand α q u
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun u => by
    dsimp only [momentFiber, realOrderIntegrand]
    rw [mul_comm (Real.cosh u) q]
    ring)

/-- Absolute integrability of the first q-moment of the literal real-order
K integral. This is proved from the positive product kernel. -/
theorem realOrderK_first_moment_integrable {α : ℝ} (hα : |α| ≤ 1) :
    IntegrableOn (fun q : ℝ => q * realOrderK α q) (Ioi 0) := by
  have h := (momentFiber_joint_integrable hα).integral_prod_right
  simpa only [momentFiber_u_integral] using h

/-- Exact Fubini reduction of the first real-order K Mellin moment.
Evaluating the remaining cosh integral by Beta is a separate task. -/
theorem realOrderK_first_moment {α : ℝ} (hα : |α| ≤ 1) :
    (∫ q in Ioi (0 : ℝ), q * realOrderK α q) =
      ∫ u in Ioi (0 : ℝ), firstMomentDensity α u := by
  have h := integral_integral_swap (momentFiber_joint_integrable hα)
  simpa only [firstMomentDensity_eq_q_integral, momentFiber_u_integral] using h.symm

/-- An explicit uniform positive first-moment bound. Its numerical constant
is only an elementary integral envelope, not an exceptional spectral gain. -/
theorem realOrderK_first_moment_le_two {α : ℝ} (hα : |α| ≤ 1) :
    (∫ q in Ioi (0 : ℝ), q * realOrderK α q) ≤ 2 := by
  rw [realOrderK_first_moment hα, ← expEnvelope_integral]
  apply integral_mono_ae (firstMomentDensity_integrable hα) expEnvelope_integrable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact firstMomentDensity_le_exp hα hu.le

/-- The proved Mellin moment is monotone in the absolute real Bessel order. -/
theorem realOrderK_first_moment_mono_abs {α β : ℝ}
    (hβ : |β| ≤ 1) (hαβ : |α| ≤ |β|) :
    (∫ q in Ioi (0 : ℝ), q * realOrderK α q) ≤
      ∫ q in Ioi (0 : ℝ), q * realOrderK β q := by
  have hα : |α| ≤ 1 := hαβ.trans hβ
  rw [realOrderK_first_moment hα, realOrderK_first_moment hβ]
  exact integral_mono (firstMomentDensity_integrable hα)
    (firstMomentDensity_integrable hβ) (firstMomentDensity_mono_abs hαβ)

/-- Specialization to the actual exceptional Bessel-order interval. -/
theorem exceptionalK_first_moment_integrable {α : ℝ}
    (hα : |α| ≤ (7 / 32 : ℝ)) :
    IntegrableOn (fun q : ℝ => q * realOrderK α q) (Ioi 0) :=
  realOrderK_first_moment_integrable (by linarith)

theorem exceptionalK_first_moment_le_two {α : ℝ}
    (hα : |α| ≤ (7 / 32 : ℝ)) :
    (∫ q in Ioi (0 : ℝ), q * realOrderK α q) ≤ 2 :=
  realOrderK_first_moment_le_two (by linarith)

end
end ImbalancedChen.Part3.RealOrderKFirstMoment20261025a
