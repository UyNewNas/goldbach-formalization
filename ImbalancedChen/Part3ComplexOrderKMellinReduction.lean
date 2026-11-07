import ImbalancedChen.Part3ComplexOrderKEntire
import ImbalancedChen.Part3RealOrderKMellinReduction
import Mathlib.MeasureTheory.Integral.Prod

/-! SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
Full complex order and complex Mellin exponent: absolute double
integrability and actual Gamma-Laplace Fubini reduction on Re s>|Re nu|.
No formula or analytic-continuation hypothesis is an input. -/

namespace ImbalancedChen.Part3.ComplexOrderKMellinReduction20261025a
noncomputable section
open Set MeasureTheory Filter
open ComplexOrderKBridgeSourceOnly
open RealOrderKExceptionalSourceOnly
open RealOrderKMellinReduction20261025a (mellinDensity mellinDensity_integrable)

def complexMellinFiber (ν s : ℂ) (u q : ℝ) : ℂ :=
  Complex.exp ((Real.log q : ℂ) * (s - 1)) * complexOrderIntegrand ν q u

def complexMellinDensity (ν s : ℂ) (u : ℝ) : ℂ :=
  Complex.cosh (ν * (u : ℂ)) * ((1 / Real.cosh u : ℝ) : ℂ) ^ s

private def positiveFiber (α σ u q : ℝ) : ℝ :=
  Real.exp (Real.log q * (σ - 1)) * Real.exp (-q * Real.cosh u) * Real.cosh (α * u)

private theorem positiveFiber_nonneg (α σ u q : ℝ) : 0 ≤ positiveFiber α σ u q := by
  unfold positiveFiber
  positivity

private theorem positiveFiber_integrable (α σ u : ℝ) (hσ : 0 < σ) :
    IntegrableOn (positiveFiber α σ u) (Ioi 0) := by
  have hbase : IntegrableOn (fun q : ℝ => q ^ (σ - 1) *
      Real.exp (-(Real.cosh u * q))) (Ioi 0) := by
    simpa only [Real.rpow_one, neg_mul] using
      integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (s := σ - 1)
        (b := Real.cosh u) (by linarith) le_rfl (Real.cosh_pos u)
  apply (hbase.mul_const (Real.cosh (α * u))).congr_fun _ measurableSet_Ioi
  intro q hq
  simp only [positiveFiber, Real.rpow_def_of_pos hq, mul_comm q (Real.cosh u), neg_mul]

private theorem positiveFiber_integral (α σ u : ℝ) (hσ : 0 < σ) :
    (∫ q in Ioi (0 : ℝ), positiveFiber α σ u q) =
      Real.Gamma σ * mellinDensity α σ u := by
  have heq : (∫ q in Ioi (0 : ℝ), positiveFiber α σ u q) =
      ∫ q in Ioi (0 : ℝ), (q ^ (σ - 1) * Real.exp (-(Real.cosh u * q))) *
        Real.cosh (α * u) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro q hq
    simp only [positiveFiber, Real.rpow_def_of_pos hq, mul_comm q (Real.cosh u), neg_mul]
  rw [heq, integral_mul_const, Real.integral_rpow_mul_exp_neg_mul_Ioi hσ (Real.cosh_pos u)]
  unfold mellinDensity
  ring

private theorem positiveFiber_joint_integrable {α σ : ℝ} (h : |α| < σ) :
    Integrable (fun p : ℝ × ℝ => positiveFiber α σ p.1 p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hσ : 0 < σ := (abs_nonneg α).trans_lt h
  have hm : Measurable (fun p : ℝ × ℝ => positiveFiber α σ p.1 p.2) := by
    unfold positiveFiber
    fun_prop
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · exact ae_of_all _ (fun u => positiveFiber_integrable α σ u hσ)
  · have heq : (fun u : ℝ => ∫ q in Ioi (0 : ℝ), ‖positiveFiber α σ u q‖) =
        fun u : ℝ => Real.Gamma σ * mellinDensity α σ u := by
      funext u
      rw [← positiveFiber_integral α σ u hσ]
      apply integral_congr_ae
      exact ae_of_all _ (fun q => by rw [Real.norm_eq_abs, abs_of_nonneg (positiveFiber_nonneg _ _ _ _)])
    simpa only [heq] using (mellinDensity_integrable h).const_mul (Real.Gamma σ)

theorem complexMellinFiber_norm_le (ν s : ℂ) (u q : ℝ) :
    ‖complexMellinFiber ν s u q‖ ≤ positiveFiber ν.re s.re u q := by
  have hnorm : ‖Complex.exp ((Real.log q : ℂ) * (s - 1))‖ =
      Real.exp (Real.log q * (s.re - 1)) := by
    simp [Complex.norm_exp]
  rw [complexMellinFiber, norm_mul, hnorm]
  have hh := mul_le_mul_of_nonneg_left (complexOrderIntegrand_norm_le_real ν q u)
    (Real.exp_pos (Real.log q * (s.re - 1))).le
  simpa only [positiveFiber, realOrderIntegrand, mul_assoc] using hh

/-- Actual full double absolute convergence, with both complex parameters free. -/
theorem complexMellinFiber_joint_integrable {ν s : ℂ} (hs : |ν.re| < s.re) :
    Integrable (fun p : ℝ × ℝ => complexMellinFiber ν s p.1 p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hm : Measurable (fun p : ℝ × ℝ => complexMellinFiber ν s p.1 p.2) := by
    unfold complexMellinFiber complexOrderIntegrand
    fun_prop
  exact (positiveFiber_joint_integrable hs).mono' hm.aestronglyMeasurable
    (ae_of_all _ (fun p => complexMellinFiber_norm_le ν s p.1 p.2))

theorem complexMellinFiber_eq_actual (ν s : ℂ) (u : ℝ) {q : ℝ} (hq : 0 < q) :
    complexMellinFiber ν s u q = (q : ℂ) ^ (s - 1) * complexOrderIntegrand ν q u := by
  rw [complexMellinFiber, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hq.ne'),
    ← Complex.ofReal_log hq.le]

theorem complexMellinFiber_u_integral (ν s : ℂ) {q : ℝ} (hq : 0 < q) :
    (∫ u in Ioi (0 : ℝ), complexMellinFiber ν s u q) =
      (q : ℂ) ^ (s - 1) * complexOrderK ν q := by
  simp_rw [complexMellinFiber_eq_actual ν s _ hq]
  rw [integral_const_mul]
  rfl

theorem complexMellinFiber_q_integral (ν s : ℂ) (u : ℝ) (hs : 0 < s.re) :
    (∫ q in Ioi (0 : ℝ), complexMellinFiber ν s u q) =
      Complex.Gamma s * complexMellinDensity ν s u := by
  have heq : (∫ q in Ioi (0 : ℝ), complexMellinFiber ν s u q) =
      ∫ q in Ioi (0 : ℝ), ((q : ℂ) ^ (s - 1) *
        Complex.exp (-((Real.cosh u : ℂ) * (q : ℂ)))) * Complex.cosh (ν * (u : ℂ)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro q hq
    rw [complexMellinFiber_eq_actual ν s u hq]
    unfold complexOrderIntegrand
    rw [Complex.ofReal_exp]
    have he : ((-q * Real.cosh u : ℝ) : ℂ) = -((Real.cosh u : ℂ) * (q : ℂ)) := by
      push_cast
      ring
    rw [he]
    ring
  rw [heq, integral_mul_const, Complex.integral_cpow_mul_exp_neg_mul_Ioi hs (Real.cosh_pos u)]
  unfold complexMellinDensity
  push_cast
  ring

theorem complexOrderK_mellin_integrable {ν s : ℂ} (hs : |ν.re| < s.re) :
    IntegrableOn (fun q : ℝ => (q : ℂ) ^ (s - 1) * complexOrderK ν q) (Ioi 0) := by
  apply (complexMellinFiber_joint_integrable hs).integral_prod_right.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
  exact complexMellinFiber_u_integral ν s hq

/-- Genuine Gamma reduction by Fubini; only the explicit cosh integral remains. -/
theorem complexOrderK_mellin_reduction {ν s : ℂ} (hs : |ν.re| < s.re) :
    (∫ q in Ioi (0 : ℝ), (q : ℂ) ^ (s - 1) * complexOrderK ν q) =
      Complex.Gamma s * ∫ u in Ioi (0 : ℝ), complexMellinDensity ν s u := by
  have hs0 : 0 < s.re := (abs_nonneg ν.re).trans_lt hs
  calc
    _ = ∫ q in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ), complexMellinFiber ν s u q := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
      exact (complexMellinFiber_u_integral ν s hq).symm
    _ = ∫ u in Ioi (0 : ℝ), ∫ q in Ioi (0 : ℝ), complexMellinFiber ν s u q :=
      (integral_integral_swap (complexMellinFiber_joint_integrable hs)).symm
    _ = _ := by simp only [complexMellinFiber_q_integral ν s _ hs0, integral_const_mul]

end
end ImbalancedChen.Part3.ComplexOrderKMellinReduction20261025a
