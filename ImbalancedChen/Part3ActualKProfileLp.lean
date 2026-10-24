import ImbalancedChen.Part3ImaginaryOrderKPositiveAxis
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Tactic

/-!
SOURCEONLY, 2026-10-24. UNCOMPILED.  This is the actual full-line
Laplace profile for the already defined positive-axis `imaginaryOrderK`.
The full-line square integral below keeps the factor two explicitly.
-/

namespace ImbalancedChen.Part3.P3ActualKProfileLpSourceOnly

noncomputable section

open Set MeasureTheory
open ImbalancedChen.Part3.ImaginaryOrderKBesselSourceOnly

def evenLaplaceProfile (q u : ℝ) : ℂ :=
  (Real.exp (-q * Real.cosh u) : ℂ)

theorem evenLaplaceProfile_continuous (q : ℝ) :
    Continuous (evenLaplaceProfile q) := by
  unfold evenLaplaceProfile
  fun_prop

theorem evenLaplaceProfile_even (q u : ℝ) :
    evenLaplaceProfile q (-u) = evenLaplaceProfile q u := by
  simp [evenLaplaceProfile, Real.cosh_neg]

private theorem half_abs_le_cosh (u : ℝ) :
    |u| / 2 ≤ Real.cosh u := by
  have hp := half_le_cosh u
  have hn := half_le_cosh (-u)
  rw [Real.cosh_neg] at hn
  have habs : |u| ≤ 2 * Real.cosh u :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  linarith

private theorem exp_abs_majorant_integrable {q : ℝ} (hq : 0 < q) :
    Integrable (fun u : ℝ => Real.exp (-(q / 2) * |u|)) := by
  have hleft : IntegrableOn
      (fun u : ℝ => Real.exp (-(q / 2) * |u|)) (Iic 0) := by
    refine (integrableOn_exp_mul_Iic (show 0 < q / 2 by positivity) 0).congr_fun ?_
      measurableSet_Iic
    intro u hu
    have habs : |u| = -u := abs_eq_neg_self.mpr hu
    simp only [habs]
    congr 1
    ring
  have hright : IntegrableOn
      (fun u : ℝ => Real.exp (-(q / 2) * |u|)) (Ioi 0) := by
    refine (integrableOn_exp_mul_Ioi (show -(q / 2) < 0 by linarith) 0).congr_fun ?_
      measurableSet_Ioi
    intro u hu
    rw [abs_of_pos hu]
  simpa only [Iic_union_Ioi, integrableOn_univ] using hleft.union hright

private theorem evenLaplaceProfile_norm (q u : ℝ) :
    ‖evenLaplaceProfile q u‖ = Real.exp (-q * Real.cosh u) := by
  simp [evenLaplaceProfile, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

private theorem evenLaplaceProfile_norm_le_majorant {q : ℝ} (hq : 0 < q)
    (u : ℝ) :
    ‖evenLaplaceProfile q u‖ ≤ Real.exp (-(q / 2) * |u|) := by
  rw [evenLaplaceProfile_norm]
  apply Real.exp_le_exp.mpr
  have hm := mul_le_mul_of_nonneg_left (half_abs_le_cosh u) hq.le
  nlinarith

theorem evenLaplaceProfile_integrable {q : ℝ} (hq : 0 < q) :
    Integrable (evenLaplaceProfile q) := by
  exact (exp_abs_majorant_integrable hq).mono'
    (evenLaplaceProfile_continuous q).aestronglyMeasurable
    (Filter.Eventually.of_forall (evenLaplaceProfile_norm_le_majorant hq))

private theorem evenLaplaceProfile_norm_sq (q u : ℝ) :
    ‖evenLaplaceProfile q u‖ ^ 2 =
      Real.exp (-(2 * q) * Real.cosh u) := by
  rw [evenLaplaceProfile_norm, pow_two, ← Real.exp_add]
  congr 1
  ring

theorem evenLaplaceProfile_sq_integrable {q : ℝ} (hq : 0 < q) :
    Integrable (fun u : ℝ => ‖evenLaplaceProfile q u‖ ^ 2) := by
  have hExp : Integrable
      (fun u : ℝ => Real.exp (-(2 * q) * Real.cosh u)) := by
    simpa only [evenLaplaceProfile, Complex.ofReal_re] using
      (evenLaplaceProfile_integrable (q := 2 * q) (by linarith)).re
  exact hExp.congr (Filter.Eventually.of_forall
    (fun u => (evenLaplaceProfile_norm_sq q u).symm))

theorem evenLaplaceProfile_memLp_two {q : ℝ} (hq : 0 < q) :
    MemLp (evenLaplaceProfile q) 2 volume := by
  exact (memLp_two_iff_integrable_sq_norm
    (evenLaplaceProfile_continuous q).aestronglyMeasurable).2
    (evenLaplaceProfile_sq_integrable hq)

/-- The full-line L² mass is twice the positive-axis `K₀(2q)` integral. -/
theorem evenLaplaceProfile_norm_sq_integral {q : ℝ} (hq : 0 < q) :
    (∫ u : ℝ, ‖evenLaplaceProfile q u‖ ^ 2) =
      2 * imaginaryOrderK 0 (2 * q) := by
  calc
    (∫ u : ℝ, ‖evenLaplaceProfile q u‖ ^ 2) =
        ∫ u : ℝ, Real.exp (-(2 * q) * Real.cosh |u|) := by
      congr 1
      funext u
      rw [evenLaplaceProfile_norm_sq, Real.cosh_abs]
    _ = 2 * ∫ u in Ioi (0 : ℝ),
        Real.exp (-(2 * q) * Real.cosh u) := by
      exact integral_comp_abs (f := fun u : ℝ =>
        Real.exp (-(2 * q) * Real.cosh u))
    _ = 2 * imaginaryOrderK 0 (2 * q) := by
      simp [imaginaryOrderK, kIntegrand]

end

end ImbalancedChen.Part3.P3ActualKProfileLpSourceOnly
