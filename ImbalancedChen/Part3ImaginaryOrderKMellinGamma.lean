import ImbalancedChen.Part3ImaginaryOrderKMellinReduction
import ImbalancedChen.Part3ComplexBetaReciprocalTail
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

/-!
CODE_ONLY / SOURCEONLY / UNCOMPILED, 2026-10-25. No acceptance credit.

Gamma-product Mellin normalization of the literal imaginaryOrderK t q.
Its defining oscillation is cos(2*t*u), so the Gamma arguments are
s/2+I*t and s/2-I*t. The actual q-Mellin integrability and Fubini theorem,
the exp(2u) Euler-tail pullback and the complex reciprocal-tail Beta
evaluation are all source proofs, not premises of the final theorem.

This closes this one special-function normalization in uncompiled source.
KL Plancherel, automorphic spectral normalization and the original target
theorems remain OPEN.
-/

namespace ImbalancedChen.Part3.ImaginaryOrderKMellinGamma20261025a

noncomputable section
open Set MeasureTheory Filter
open ImaginaryOrderKBesselSourceOnly
open ImaginaryOrderKMellinReduction20261025a
open ImbalancedChen.Part3ComplexBetaHalfLineGamma (halflineKernel)
open ComplexBetaReciprocalTail20261025a

def mellinA (t s : ℝ) : ℂ := (s : ℂ) / 2 + (t : ℂ) * Complex.I
def mellinB (t s : ℝ) : ℂ := (s : ℂ) / 2 - (t : ℂ) * Complex.I

private theorem mellinAB_sum (t s : ℝ) : mellinA t s + mellinB t s = (s : ℂ) := by
  dsimp only [mellinA, mellinB]
  ring

private theorem mellinBA_sum (t s : ℝ) : mellinB t s + mellinA t s = (s : ℂ) := by
  rw [add_comm, mellinAB_sum]

def complexBetaTail (t s x : ℝ) : ℂ :=
  halflineKernel (mellinA t s) (mellinB t s) x +
    halflineKernel (mellinB t s) (mellinA t s) x

private def expTailProfile (t s x : ℝ) : ℂ :=
  (Real.exp x : ℂ) * complexBetaTail t s (Real.exp x)

private theorem real_exp_cpow (x : ℝ) (z : ℂ) :
    (Real.exp x : ℂ) ^ z = Complex.exp ((x : ℂ) * z) := by
  rw [Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.exp_pos x).ne'),
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp]

private theorem weighted_real_exp_cpow (x : ℝ) (z : ℂ) :
    (Real.exp x : ℂ) * (Real.exp x : ℂ) ^ (z - 1) =
      Complex.exp ((x : ℂ) * z) := by
  rw [real_exp_cpow, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  ring

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

private theorem complex_exponential_pair (y : ℝ) :
    Complex.exp ((y : ℂ) * Complex.I) + Complex.exp (-(y : ℂ) * Complex.I) =
      2 * (Real.cos y : ℂ) := by
  rw [Complex.ofReal_cos, Complex.cos]
  ring

private theorem expTailProfile_eq_cosine (t s u : ℝ) :
    expTailProfile t s (2 * u) =
      2 * (Real.exp (u * s) : ℂ) * (Real.cos (2 * t * u) : ℂ) /
        ((1 + Real.exp (2 * u)) ^ s : ℝ) := by
  have hp : (Real.exp (2 * u) : ℂ) *
      (Real.exp (2 * u) : ℂ) ^ (mellinA t s - 1) =
        (Real.exp (u * s) : ℂ) *
          Complex.exp (((2 * t * u : ℝ) : ℂ) * Complex.I) := by
    rw [weighted_real_exp_cpow, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    dsimp only [mellinA]
    push_cast
    ring
  have hn : (Real.exp (2 * u) : ℂ) *
      (Real.exp (2 * u) : ℂ) ^ (mellinB t s - 1) =
        (Real.exp (u * s) : ℂ) *
          Complex.exp (-((2 * t * u : ℝ) : ℂ) * Complex.I) := by
    rw [weighted_real_exp_cpow, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    dsimp only [mellinB]
    push_cast
    ring
  have hsum : (Real.exp (2 * u) : ℂ) *
      ((Real.exp (2 * u) : ℂ) ^ (mellinA t s - 1) +
        (Real.exp (2 * u) : ℂ) ^ (mellinB t s - 1)) =
      2 * (Real.exp (u * s) : ℂ) * (Real.cos (2 * t * u) : ℂ) := by
    rw [mul_add, hp, hn, ← mul_add, complex_exponential_pair]
    ring
  dsimp only [expTailProfile, complexBetaTail, halflineKernel]
  simp only [mellinAB_sum, mellinBA_sum,
    ← Complex.ofReal_cpow (by positivity : (0 : ℝ) ≤ 1 + Real.exp (2 * u)) s]
  rw [← add_div, ← mul_div_assoc, hsum]

/-- The concrete exp(2u) pullback of the actual oscillatory K density. -/
theorem imaginaryMellinDensity_eq_expTailProfile (t s u : ℝ) :
    (imaginaryMellinDensity t s u : ℂ) =
      (((2 : ℝ) ^ s / 2 : ℝ) : ℂ) * expTailProfile t s (2 * u) := by
  have hpow : (1 / Real.cosh u) ^ s =
      (2 : ℝ) ^ s * Real.exp (u * s) / (1 + Real.exp (2 * u)) ^ s := by
    rw [inverse_cosh_eq_exp,
      Real.div_rpow (by positivity) (by positivity) s,
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Real.exp_pos u).le,
      ← Real.exp_mul]
  rw [imaginaryMellinDensity, Complex.ofReal_mul, hpow,
    expTailProfile_eq_cosine]
  push_cast
  ring

/-- Exact complex paired-tail representation of the actual real cosine
integral, including the full factor from exp(2u). -/
theorem imaginaryMellinDensity_integral_eq_betaTail (t s : ℝ) :
    ((∫ u in Ioi (0 : ℝ), imaginaryMellinDensity t s u) : ℂ) =
      (((2 : ℝ) ^ s / 4 : ℝ) : ℂ) *
        ∫ x in Ioi (1 : ℝ), complexBetaTail t s x := by
  have hexp : (∫ x in Ioi (0 : ℝ), expTailProfile t s x) =
      ∫ x in Ioi (1 : ℝ), complexBetaTail t s x := by
    simpa only [expTailProfile, Complex.real_smul, Real.exp_zero] using
      integral_comp_exp_Ioi (complexBetaTail t s) 0
  have hscale : (∫ u in Ioi (0 : ℝ), expTailProfile t s (2 * u)) =
      (1 / 2 : ℂ) * ∫ x in Ioi (0 : ℝ), expTailProfile t s x := by
    simpa only [mul_zero, Complex.real_smul, inv_eq_one_div,
      Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
      integral_comp_mul_left_Ioi (expTailProfile t s) 0
        (b := (2 : ℝ)) (by norm_num)
  calc
    ((∫ u in Ioi (0 : ℝ), imaginaryMellinDensity t s u) : ℂ) =
        ∫ u in Ioi (0 : ℝ), (imaginaryMellinDensity t s u : ℂ) :=
      integral_ofReal.symm
    _ = (((2 : ℝ) ^ s / 2 : ℝ) : ℂ) *
        ∫ u in Ioi (0 : ℝ), expTailProfile t s (2 * u) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all _ (imaginaryMellinDensity_eq_expTailProfile t s)
    _ = (((2 : ℝ) ^ s / 4 : ℝ) : ℂ) *
        ∫ x in Ioi (1 : ℝ), complexBetaTail t s x := by
      rw [hscale, hexp]
      push_cast
      ring

private theorem complexBetaTail_integral_eq_gamma (t : ℝ) {s : ℝ} (hs : 0 < s) :
    (∫ x in Ioi (1 : ℝ), complexBetaTail t s x) =
      Complex.Gamma (mellinA t s) * Complex.Gamma (mellinB t s) /
        Complex.Gamma (s : ℂ) := by
  have ha : 0 < (mellinA t s).re := by
    have hre : (mellinA t s).re = s / 2 := by simp [mellinA]
    rw [hre]
    exact div_pos hs (by norm_num)
  have hb : 0 < (mellinB t s).re := by
    have hre : (mellinB t s).re = s / 2 := by simp [mellinB]
    rw [hre]
    exact div_pos hs (by norm_num)
  have h := halflineKernel_paired_tail_eq_gamma ha hb
  simpa only [complexBetaTail, mellinAB_sum] using h

/-- Gamma-product Mellin normalization of the actual K_{2it} integral.
The q-Mellin moment on the left is real and is embedded into C only to
state the exact complex Gamma product on the right. -/
theorem imaginaryOrderK_mellin_eq_gamma (t : ℝ) {s : ℝ} (hs : 0 < s) :
    ((∫ q in Ioi (0 : ℝ), q ^ (s - 1) * imaginaryOrderK t q) : ℂ) =
      ((2 : ℝ) ^ (s - 2) : ℂ) *
        Complex.Gamma (mellinA t s) * Complex.Gamma (mellinB t s) := by
  have hgamma : (Real.Gamma s : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.Gamma_pos_of_pos hs).ne'
  have htwo : (2 : ℝ) ^ (s - 2) = (2 : ℝ) ^ s / 4 := by
    rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_two]
    norm_num
  rw [imaginaryOrderK_mellin_reduction t hs, Complex.ofReal_mul,
    imaginaryMellinDensity_integral_eq_betaTail,
    complexBetaTail_integral_eq_gamma t hs, Complex.Gamma_ofReal, htwo]
  push_cast
  field_simp [hgamma] <;> ring

end
end ImbalancedChen.Part3.ImaginaryOrderKMellinGamma20261025a
