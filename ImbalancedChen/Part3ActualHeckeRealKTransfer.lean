import ImbalancedChen.Part3ActualHeckeDivisibleFourier
import ImbalancedChen.Part3QuotientRealKFourierCoefficient

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT, 2026-10-26.
The literal normalized two-branch prime-Hecke expression of an actual
quotient L2 real-order Maass function has K amplitude rho(m)+rho(p^2*m)
at every nonzero index p*m. The original quotient PDE and L2 norm pay for
both original K coefficients. The square roots of p, p*y and y/p are all
cancelled by explicit identities. This is not a Hecke automorphy theorem,
an eigenvalue relation, or a spectral-completeness assumption.
-/

namespace ImbalancedChen.Part3.ActualHeckeRealKTransfer20261026b
noncomputable section
open Set MeasureTheory
open ActualHeckeDivisibleFourier20261026b ActualHeckeTranslationProjector20261026b
open QuotientRealKFourierCoefficient20261026b ActualPoincareSpectralCoefficient20261026a
open ActualMaassFourierODE20261026a ActualFourierBesselConjugation20261026a
open Gamma0QuotientCellPushforward20261025a ComplexOrderKBridgeSourceOnly

variable (N : ℕ) [NeZero N] (U : Gamma0OrbitSpace N → ℂ)
  (hU : Continuous (testLift N U)) (hU2 : MemLp U 2 (carrierPushforward N))
  (hC2 : ContDiffOn ℝ 2 (maassChart N U) upperDomain)
  (nu : ℝ) (hnu : 0 ≤ nu)
  (hPDE : ∀ z ∈ upperDomain,
    -(z.2 : ℂ)^2 * (partialX (partialX (maassChart N U)) z +
      partialY (partialY (maassChart N U)) z) = (1/4-(nu : ℂ)^2)*maassChart N U z)

/-- The exact real-K amplitude transfer at the divisible branch. All
regularity and L2 hypotheses concern the original quotient Maass function. -/
theorem actual_hecke_realK_divisible (p : ℕ) (hp : 0 < p)
    {m : ℤ} (hm : m ≠ 0) {y : ℝ} (hy : 0 < y) :
    coefficient (primeHeckeExpression p (maassChart N U)) ((p : ℤ)*m) y =
      (quotientRho N U nu m + quotientRho N U nu ((p : ℤ)*((p : ℤ)*m))) *
        (Real.sqrt y : ℂ) * complexOrderK (nu : ℂ) (2*Real.pi*|(((p : ℤ)*m : ℤ) : ℝ)|*y) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hpZ : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne'
  have hppm : (p : ℤ)*((p : ℤ)*m) ≠ 0 := mul_ne_zero hpZ (mul_ne_zero hpZ hm)
  have hargUp : 2*Real.pi*|(m : ℝ)|*((p : ℝ)*y) =
      2*Real.pi*|(((p : ℤ)*m : ℤ) : ℝ)|*y := by
    simp only [Int.cast_mul, Int.cast_natCast, abs_mul, abs_of_pos hpR]
    ring
  have hargDown : 2*Real.pi*|(((p : ℤ)*((p : ℤ)*m) : ℤ) : ℝ)|*(y/(p : ℝ)) =
      2*Real.pi*|(((p : ℤ)*m : ℤ) : ℝ)|*y := by
    simp only [Int.cast_mul, Int.cast_natCast, abs_mul, abs_of_pos hpR]
    field_simp [hpR.ne'] <;> ring
  have hrootUp : (Real.sqrt ((p : ℝ)*y) : ℂ) =
      (Real.sqrt (p : ℝ) : ℂ) * (Real.sqrt y : ℂ) := by
    rw [Real.sqrt_mul hpR.le, Complex.ofReal_mul]
  have hrootDown : (Real.sqrt (y/(p : ℝ)) : ℂ) =
      (Real.sqrt y : ℂ) / (Real.sqrt (p : ℝ) : ℂ) := by
    rw [Real.sqrt_div hy.le, Complex.ofReal_div]
  have hs : (Real.sqrt (p : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hpR).ne'
  have hsq : (Real.sqrt (p : ℝ) : ℂ)^2 = (p : ℂ) := by
    exact_mod_cast Real.sq_sqrt hpR.le
  rw [coefficient_primeHeckeExpression_divisible p hp hC2.continuousOn
    (maassChart_periodic N U) m hy]
  rw [← actualTestFourier_eq_coefficient N U m ((p : ℝ)*y),
    ← actualTestFourier_eq_coefficient N U ((p : ℤ)*((p : ℤ)*m)) (y/(p : ℝ))]
  rw [actual_quotient_fourier_eq_realK N U hU hU2 hC2 nu hnu hPDE hm (mul_pos hpR hy),
    actual_quotient_fourier_eq_realK N U hU hU2 hC2 nu hnu hPDE hppm (div_pos hy hpR),
    hargUp, hargDown, hrootUp, hrootDown, ← hsq]
  field_simp [hs] <;> ring

/-- The transferred amplitude can be read at any actual positive height;
actual K positivity rules out a hidden zero denominator, including nu=0. -/
theorem actual_hecke_realK_amplitude_value (p : ℕ) (hp : 0 < p)
    {m : ℤ} (hm : m ≠ 0) {y : ℝ} (hy : 0 < y) :
    quotientRho N U nu m + quotientRho N U nu ((p : ℤ)*((p : ℤ)*m)) =
      coefficient (primeHeckeExpression p (maassChart N U)) ((p : ℤ)*m) y /
        ((Real.sqrt y : ℂ) * complexOrderK (nu : ℂ) (modeFrequency ((p : ℤ)*m)*y)) := by
  have hpZ : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne'
  have hpm : (p : ℤ)*m ≠ 0 := mul_ne_zero hpZ hm
  have hden : (Real.sqrt y : ℂ) *
      complexOrderK (nu : ℂ) (modeFrequency ((p : ℤ)*m)*y) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hy).ne')
      (RealBesselTailKSelection20261026a.actualRealK_ne_zero nu
        (mul_pos (modeFrequency_pos hpm) hy))
  apply (eq_div_iff hden).mpr
  have h := actual_hecke_realK_divisible N U hU hU2 hC2 nu hnu hPDE p hp hm hy
  simpa only [modeFrequency, mul_assoc] using h.symm

end
end ImbalancedChen.Part3.ActualHeckeRealKTransfer20261026b
