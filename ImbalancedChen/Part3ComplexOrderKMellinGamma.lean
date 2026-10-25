import ImbalancedChen.Part3ComplexOrderKMellinReduction
import ImbalancedChen.Part3ComplexBetaReciprocalTail

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
Gamma-product Mellin normalization for the actual complex-order K and
complex Mellin exponent on Re s>|Re nu|. Absolute convergence and Fubini
are supplied by the companion actual-fiber proof; exp(2u) and the genuine
complex reciprocal-tail Beta theorem evaluate the remaining integral.
No analytic-continuation hypothesis or Mellin identity is assumed.
-/

namespace ImbalancedChen.Part3.ComplexOrderKMellinGamma20261025a
noncomputable section
open Set MeasureTheory Filter
open ComplexOrderKBridgeSourceOnly ComplexOrderKMellinReduction20261025a
open ImbalancedChen.Part3ComplexBetaHalfLineGamma (halflineKernel)
open ComplexBetaReciprocalTail20261025a

def mellinA (ν s : ℂ) : ℂ := (s + ν) / 2
def mellinB (ν s : ℂ) : ℂ := (s - ν) / 2

private theorem parameters_sum (ν s : ℂ) : mellinA ν s + mellinB ν s = s := by
  unfold mellinA mellinB
  ring

private def betaTail (ν s : ℂ) (x : ℝ) : ℂ :=
  halflineKernel (mellinA ν s) (mellinB ν s) x +
    halflineKernel (mellinB ν s) (mellinA ν s) x

private def expTailProfile (ν s : ℂ) (x : ℝ) : ℂ :=
  (Real.exp x : ℂ) * betaTail ν s (Real.exp x)

private theorem real_exp_cpow (x : ℝ) (z : ℂ) :
    (Real.exp x : ℂ) ^ z = Complex.exp ((x : ℂ) * z) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)),
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp]

private theorem weighted_real_exp_cpow (x : ℝ) (z : ℂ) :
    (Real.exp x : ℂ) * (Real.exp x : ℂ) ^ (z - 1) = Complex.exp ((x : ℂ) * z) := by
  rw [real_exp_cpow, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  ring

private theorem inverse_cosh_eq_exp (u : ℝ) :
    1 / Real.cosh u = 2 * Real.exp u / (1 + Real.exp (2 * u)) := by
  have hprod : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add]; simp
  have hdouble : Real.exp (2 * u) = Real.exp u * Real.exp u := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hden : 1 + Real.exp (2 * u) = 2 * Real.exp u * Real.cosh u := by
    rw [Real.cosh_eq]
    nlinarith only [hprod, hdouble]
  rw [hden]
  field_simp [(Real.exp_ne_zero u), (Real.cosh_pos u).ne'] <;> ring

private theorem expTailProfile_eq_cosh (ν s : ℂ) (u : ℝ) :
    expTailProfile ν s (2 * u) =
      2 * Complex.exp ((u : ℂ) * s) * Complex.cosh (ν * (u : ℂ)) /
        ((1 + Real.exp (2 * u) : ℝ) : ℂ) ^ s := by
  have hp : (Real.exp (2 * u) : ℂ) * (Real.exp (2 * u) : ℂ) ^ (mellinA ν s - 1) =
      Complex.exp ((u : ℂ) * s) * Complex.exp (ν * (u : ℂ)) := by
    rw [weighted_real_exp_cpow, ← Complex.exp_add]
    congr 1
    unfold mellinA
    push_cast
    ring
  have hn : (Real.exp (2 * u) : ℂ) * (Real.exp (2 * u) : ℂ) ^ (mellinB ν s - 1) =
      Complex.exp ((u : ℂ) * s) * Complex.exp (-(ν * (u : ℂ))) := by
    rw [weighted_real_exp_cpow, ← Complex.exp_add]
    congr 1
    unfold mellinB
    push_cast
    ring
  have hsum : (Real.exp (2 * u) : ℂ) *
      ((Real.exp (2 * u) : ℂ) ^ (mellinA ν s - 1) +
        (Real.exp (2 * u) : ℂ) ^ (mellinB ν s - 1)) =
      2 * Complex.exp ((u : ℂ) * s) * Complex.cosh (ν * (u : ℂ)) := by
    rw [mul_add, hp, hn, ← mul_add, ← Complex.two_cosh]
    ring
  have hswap : mellinB ν s + mellinA ν s = s := by rw [add_comm, parameters_sum]
  unfold expTailProfile betaTail halflineKernel
  rw [parameters_sum, hswap, ← add_div, ← mul_div_assoc, hsum]

theorem complexMellinDensity_eq_expTail (ν s : ℂ) (u : ℝ) :
    complexMellinDensity ν s u = (2 : ℂ) ^ s / 2 * expTailProfile ν s (2 * u) := by
  have hpow : ((1 / Real.cosh u : ℝ) : ℂ) ^ s =
      (2 : ℂ) ^ s * Complex.exp ((u : ℂ) * s) /
        ((1 + Real.exp (2 * u) : ℝ) : ℂ) ^ s := by
    rw [inverse_cosh_eq_exp, Complex.ofReal_div,
      Complex.div_cpow_ofReal_nonneg (by positivity) (by positivity),
      Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by norm_num) (Real.exp_pos u).le,
      real_exp_cpow] <;> norm_num
  rw [complexMellinDensity, hpow, expTailProfile_eq_cosh]
  ring

theorem complexMellinDensity_integral_eq_betaTail (ν s : ℂ) :
    (∫ u in Ioi (0 : ℝ), complexMellinDensity ν s u) =
      (2 : ℂ) ^ s / 4 * ∫ x in Ioi (1 : ℝ), betaTail ν s x := by
  have hexp : (∫ x in Ioi (0 : ℝ), expTailProfile ν s x) =
      ∫ x in Ioi (1 : ℝ), betaTail ν s x := by
    simpa only [expTailProfile, Complex.real_smul, Real.exp_zero] using
      integral_comp_exp_Ioi (betaTail ν s) 0
  have hscale : (∫ u in Ioi (0 : ℝ), expTailProfile ν s (2 * u)) =
      (1 / 2 : ℂ) * ∫ x in Ioi (0 : ℝ), expTailProfile ν s x := by
    simpa only [mul_zero, Complex.real_smul, inv_eq_one_div, Complex.ofReal_div,
      Complex.ofReal_one, Complex.ofReal_ofNat] using
      integral_comp_mul_left_Ioi (expTailProfile ν s) 0 (b := (2 : ℝ)) (by norm_num)
  simp_rw [complexMellinDensity_eq_expTail]
  rw [integral_const_mul, hscale, hexp]
  ring

private theorem betaTail_integral {ν s : ℂ} (hs : |ν.re| < s.re) :
    (∫ x in Ioi (1 : ℝ), betaTail ν s x) =
      Complex.Gamma (mellinA ν s) * Complex.Gamma (mellinB ν s) / Complex.Gamma s := by
  have ha : 0 < (mellinA ν s).re := by
    have he : (mellinA ν s).re = (s.re + ν.re) / 2 := by simp [mellinA, div_eq_mul_inv]
    rw [he]
    linarith only [hs, neg_le_abs ν.re]
  have hb : 0 < (mellinB ν s).re := by
    have he : (mellinB ν s).re = (s.re - ν.re) / 2 := by simp [mellinB, div_eq_mul_inv]
    rw [he]
    linarith only [hs, le_abs_self ν.re]
  simpa only [betaTail, parameters_sum] using halflineKernel_paired_tail_eq_gamma ha hb

/-- Full actual complex-order/complex-exponent Mellin formula. Its absolute
convergence is complexOrderK_mellin_integrable from the companion module. -/
theorem complexOrderK_mellin_eq_gamma {ν s : ℂ} (hs : |ν.re| < s.re) :
    (∫ q in Ioi (0 : ℝ), (q : ℂ) ^ (s - 1) * complexOrderK ν q) =
      (2 : ℂ) ^ (s - 2) * Complex.Gamma ((s + ν) / 2) * Complex.Gamma ((s - ν) / 2) := by
  have hs0 : 0 < s.re := (abs_nonneg ν.re).trans_lt hs
  have hgamma : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs0
  have htwo : (2 : ℂ) ^ (s - 2) = (2 : ℂ) ^ s / 4 := by
    rw [Complex.cpow_sub _ _ (by norm_num : (2 : ℂ) ≠ 0), Complex.cpow_two] <;> norm_num
  rw [complexOrderK_mellin_reduction hs, complexMellinDensity_integral_eq_betaTail,
    betaTail_integral hs, htwo]
  unfold mellinA mellinB
  field_simp [hgamma] <;> ring

end
end ImbalancedChen.Part3.ComplexOrderKMellinGamma20261025a
