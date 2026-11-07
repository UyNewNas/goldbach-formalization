import ImbalancedChen.Part3RealBetaHalfLineGamma

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

Complex Euler Beta on the positive real halfline. Both parameters may have
nonzero imaginary part; only their real parts are positive. Convergence is
transported from the pinned complex compact Beta integral by the actual
Jacobian of t/(1+t). No analytic-continuation or integral-evaluation premise
is introduced. The real module is used only for this real change of variable.

The spectral decomposition and original dispersion suppliers remain open.
-/

namespace ImbalancedChen.Part3ComplexBetaHalfLineGamma

noncomputable section
open Set MeasureTheory
open Part3RealBetaHalfLineGamma (halflineToUnit halflineToUnit_hasDerivAt
  halflineToUnit_injOn halflineToUnit_image)

def compactKernel (a b : ℂ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ (a - 1) * (1 - (x : ℂ)) ^ (b - 1)

def halflineKernel (a b : ℂ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ (a - 1) / ((1 + t : ℝ) : ℂ) ^ (a + b)

theorem integrableOn_compactKernel {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    IntegrableOn (compactKernel a b) (Ioo 0 1) := by
  exact (Complex.betaIntegral_convergent ha hb).1.mono_set Ioo_subset_Ioc_self

theorem integral_compactKernel_eq_beta (a b : ℂ) :
    (∫ x in Ioo (0 : ℝ) 1, compactKernel a b x) = Complex.betaIntegral a b := by
  unfold Complex.betaIntegral compactKernel
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo]

theorem integral_compactKernel_eq_gamma {a b : ℂ}
    (ha : 0 < a.re) (hb : 0 < b.re) :
    (∫ x in Ioo (0 : ℝ) 1, compactKernel a b x) =
      Complex.Gamma a * Complex.Gamma b / Complex.Gamma (a + b) := by
  rw [integral_compactKernel_eq_beta]
  have hab : 0 < (a + b).re := by simpa only [Complex.add_re] using add_pos ha hb
  apply (eq_div_iff (Complex.Gamma_ne_zero_of_re_pos hab)).2
  simpa only [mul_comm] using (Complex.Gamma_mul_Gamma_eq_betaIntegral ha hb).symm

/-- Positive real bases ensure the principal cpow division laws apply.
The scalar Jacobian remains real and multiplies the complex integrand. -/
theorem halfline_jacobian_kernel (a b : ℂ) {t : ℝ} (ht : 0 < t) :
    |1 / (1 + t) ^ 2| • compactKernel a b (halflineToUnit t) =
      halflineKernel a b t := by
  have hd : 0 < 1 + t := by linarith
  have hdC : ((1 + t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd.ne'
  have hsubR : 1 - t / (1 + t) = 1 / (1 + t) := by
    field_simp [hd.ne']
    <;> ring
  have hsubC : 1 - ((t / (1 + t) : ℝ) : ℂ) =
      (1 : ℂ) / ((1 + t : ℝ) : ℂ) := by
    exact_mod_cast hsubR
  have hpow : ((1 + t : ℝ) : ℂ) ^ (a + b) =
      ((1 + t : ℝ) : ℂ) ^ 2 * ((1 + t : ℝ) : ℂ) ^ (a - 1) *
        ((1 + t : ℝ) : ℂ) ^ (b - 1) := by
    calc
      ((1 + t : ℝ) : ℂ) ^ (a + b) =
          ((1 + t : ℝ) : ℂ) ^ ((2 : ℂ) + (a - 1) + (b - 1)) := by
        congr 1
        ring
      _ = _ := by
        rw [Complex.cpow_add _ _ hdC, Complex.cpow_add _ _ hdC, Complex.cpow_two]
  rw [Complex.real_smul, abs_of_nonneg (by positivity : 0 ≤ 1 / (1 + t) ^ 2)]
  simp only [compactKernel, halflineToUnit, halflineKernel]
  rw [hsubC, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_pow,
    Complex.ofReal_div, Complex.div_cpow_ofReal_nonneg ht.le hd.le,
    Complex.div_cpow_ofReal_nonneg zero_le_one hd.le, Complex.one_cpow, hpow]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem integrableOn_halflineKernel {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    IntegrableOn (halflineKernel a b) (Ioi 0) := by
  have hchange := integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioi
    (fun t ht => (halflineToUnit_hasDerivAt ht).hasDerivWithinAt)
    halflineToUnit_injOn (compactKernel a b)
  rw [halflineToUnit_image] at hchange
  have h := hchange.mp (integrableOn_compactKernel ha hb)
  exact h.congr_fun (fun t ht => halfline_jacobian_kernel a b ht) measurableSet_Ioi

theorem integral_halflineKernel_eq_gamma {a b : ℂ}
    (ha : 0 < a.re) (hb : 0 < b.re) :
    (∫ t in Ioi (0 : ℝ), halflineKernel a b t) =
      Complex.Gamma a * Complex.Gamma b / Complex.Gamma (a + b) := by
  have hchange := integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioi
    (fun t ht => (halflineToUnit_hasDerivAt ht).hasDerivWithinAt)
    halflineToUnit_injOn (compactKernel a b)
  rw [halflineToUnit_image] at hchange
  calc
    (∫ t in Ioi (0 : ℝ), halflineKernel a b t) =
        ∫ t in Ioi (0 : ℝ), |1 / (1 + t) ^ 2| •
          compactKernel a b (halflineToUnit t) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact (halfline_jacobian_kernel a b ht).symm
    _ = ∫ x in Ioo (0 : ℝ) 1, compactKernel a b x := hchange.symm
    _ = _ := integral_compactKernel_eq_gamma ha hb

/-- Literal cpow integrand for complex Mellin consumers. -/
theorem integrableOn_beta_halfline {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ (a - 1) / (1 + (t : ℂ)) ^ (a + b)) (Ioi 0) := by
  simpa only [halflineKernel, Complex.ofReal_add, Complex.ofReal_one] using
    integrableOn_halflineKernel ha hb

/-- Complex Euler Beta on (0,infinity), with convergence supplied above. -/
theorem integral_beta_halfline_eq_gamma {a b : ℂ}
    (ha : 0 < a.re) (hb : 0 < b.re) :
    (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (a - 1) / (1 + (t : ℂ)) ^ (a + b)) =
      Complex.Gamma a * Complex.Gamma b / Complex.Gamma (a + b) := by
  simpa only [halflineKernel, Complex.ofReal_add, Complex.ofReal_one] using
    integral_halflineKernel_eq_gamma ha hb

end
end ImbalancedChen.Part3ComplexBetaHalfLineGamma
