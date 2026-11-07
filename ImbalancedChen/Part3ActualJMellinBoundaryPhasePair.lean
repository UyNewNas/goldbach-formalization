import ImbalancedChen.Part3ActualJMellinAngularAbelLimit
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

Native principal powers on the positive and negative imaginary axes give
the two exact angular phases. Pairing opposite angular variables in the
actual J boundary integrand produces the continuous complex Poisson power
moment, with the exact factor 2*cos(pi*(s+2it)/2). No phase convention or
angular evaluation is supplied as a hypothesis.
-/

namespace ImbalancedChen.Part3.ActualJMellinBoundaryPhasePair20261026b

noncomputable section
open Complex Set
open ActualJLocalOrderHolomorphic20261026a JBesselPoissonEvenMoments20261025a
open ActualJMellinPoissonGammaReduction20261026b ActualJMellinAngularAbelLimit20261026b
open PoissonComplexPowerMoment20261026b

theorem negative_imaginary_axis_cpow (a : ℂ) {u : ℝ} (hu : 0 < u) :
    (-(I * (u : ℂ))) ^ (-a) =
      (u : ℂ) ^ (-a) * Complex.exp ((Real.pi : ℂ) * I * a / 2) := by
  have huC : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
  have hz : -(I * (u : ℂ)) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero Complex.I_ne_zero huC)
  have hl : Complex.log (-(I * (u : ℂ))) =
      Complex.log (u : ℂ) - (Real.pi : ℂ) / 2 * I := by
    rw [show -(I * (u : ℂ)) = (-I) * (u : ℂ) by ring,
      Complex.log_mul_ofReal u hu (-I) (neg_ne_zero.mpr Complex.I_ne_zero),
      Complex.log_neg_I, ← Complex.ofReal_log hu.le]
    ring
  rw [Complex.cpow_def_of_ne_zero hz, Complex.cpow_def_of_ne_zero huC, hl,
    show (Complex.log (u : ℂ) - (Real.pi : ℂ) / 2 * I) * -a =
      Complex.log (u : ℂ) * -a + (Real.pi : ℂ) * I * a / 2 by ring,
    Complex.exp_add]

theorem positive_imaginary_axis_cpow (a : ℂ) {u : ℝ} (hu : 0 < u) :
    (I * (u : ℂ)) ^ (-a) =
      (u : ℂ) ^ (-a) * Complex.exp (-((Real.pi : ℂ) * I * a / 2)) := by
  have huC : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
  have hz : I * (u : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero huC
  have hl : Complex.log (I * (u : ℂ)) =
      Complex.log (u : ℂ) + (Real.pi : ℂ) / 2 * I := by
    rw [Complex.log_mul_ofReal u hu I Complex.I_ne_zero,
      Complex.log_I, ← Complex.ofReal_log hu.le]
  rw [Complex.cpow_def_of_ne_zero hz, Complex.cpow_def_of_ne_zero huC, hl,
    show (Complex.log (u : ℂ) + (Real.pi : ℂ) / 2 * I) * -a =
      Complex.log (u : ℂ) * -a + -((Real.pi : ℂ) * I * a / 2) by ring,
    Complex.exp_add]

theorem nativeOrderWeight_even (t u : ℝ) : nativeOrderWeight t (-u) = nativeOrderWeight t u := by
  simp [nativeOrderWeight, orderPoissonIntegrand]

theorem nativeOrderWeight_eq_poissonWeight (t : ℝ) {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    nativeOrderWeight t u = poissonWeight (2 * I * (t : ℂ)) u := by
  have hx : 0 < 1 - u ^ 2 := by
    have h := abs_lt.mpr hu
    nlinarith [sq_abs u, abs_nonneg u]
  unfold nativeOrderWeight orderPoissonIntegrand poissonWeight
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, one_mul]
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    ← Complex.ofReal_log hx.le]

/-- Actual opposite-angle pairing gives a complex power moment. -/
theorem angularBoundaryIntegrand_pair (s : ℂ) (t : ℝ) {u : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    angularBoundaryIntegrand s t u + angularBoundaryIntegrand s t (-u) =
      2 * Complex.cos ((Real.pi : ℂ) * (s + 2 * I * (t : ℂ)) / 2) *
        Gamma (s + 2 * I * (t : ℂ)) *
          poissonPowerMoment (1 - (s + 2 * I * (t : ℂ))) (2 * I * (t : ℂ)) u := by
  let a : ℂ := s + 2 * I * (t : ℂ)
  have hW := nativeOrderWeight_eq_poissonWeight t (u := u) ⟨by linarith [hu.1], hu.2⟩
  have hphase : Complex.exp ((Real.pi : ℂ) * I * a / 2) +
      Complex.exp (-((Real.pi : ℂ) * I * a / 2)) =
        2 * Complex.cos ((Real.pi : ℂ) * a / 2) := by
    calc
      _ = Complex.exp (((Real.pi : ℂ) * a / 2) * I) +
          Complex.exp (-((Real.pi : ℂ) * a / 2) * I) := by
        congr 1 <;> congr 1 <;> ring
      _ = _ := (Complex.two_cos _).symm
  simp only [angularBoundaryIntegrand, Complex.ofReal_neg, mul_neg, neg_neg,
    nativeOrderWeight_even, hW]
  rw [negative_imaginary_axis_cpow _ hu.1, positive_imaginary_axis_cpow _ hu.1]
  change poissonWeight (2 * I * (t : ℂ)) u *
      ((u : ℂ) ^ (-a) * Complex.exp ((Real.pi : ℂ) * I * a / 2) * Gamma a) +
    poissonWeight (2 * I * (t : ℂ)) u *
      ((u : ℂ) ^ (-a) * Complex.exp (-((Real.pi : ℂ) * I * a / 2)) * Gamma a) = _
  calc
    _ = (Complex.exp ((Real.pi : ℂ) * I * a / 2) +
        Complex.exp (-((Real.pi : ℂ) * I * a / 2))) * Gamma a *
          ((u : ℂ) ^ (-a) * poissonWeight (2 * I * (t : ℂ)) u) := by ring
    _ = _ := by
      rw [hphase]
      unfold poissonPowerMoment
      have he : (1 - a) - 1 = -a := by ring
      change _ = 2 * Complex.cos ((Real.pi : ℂ) * a / 2) * Gamma a *
        ((u : ℂ) ^ ((1 - a) - 1) * poissonWeight (2 * I * (t : ℂ)) u)
      rw [he]

end
end ImbalancedChen.Part3.ActualJMellinBoundaryPhasePair20261026b
