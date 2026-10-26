import ImbalancedChen.Part3RealBesselTailKSelection
import ImbalancedChen.Part3ActualFourierBesselLogL2

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

The literal nonzero Fourier coefficient of a periodic C2 Maass function
with finite raw hyperbolic strip energy is a single actual real-order K
mode. The eigenvalue is 1/4-nu^2, nu>=0. The supplied hypotheses concern
the original function, its native PDE, and its actual spatial strip norm;
no coefficient ODE, coefficient L2 norm, or K expansion is assumed.

The multiplicative constant is the literal coefficient at height one
divided by K_nu(2*pi*|n|). Actual K positivity proves that the denominator
does not vanish. Quotient-to-strip geometry is a separate caller.
-/

namespace ImbalancedChen.Part3.ActualRealMaassFourierK20261026a
noncomputable section
open Set MeasureTheory
open ActualMaassFourierODE20261026a ActualFourierBesselConjugation20261026a
open ActualFourierBesselLogL220261026a RealBesselTailKSelection20261026a
open ComplexOrderKBridgeSourceOnly
attribute [local instance] Measure.Subtype.measureSpace

/-- The coefficient is fixed by an actual value of the original Fourier
coefficient, rather than chosen by an existential spectral expansion. -/
def realMaassKCoefficient (u : ℝ × ℝ → ℂ) (n : ℤ) (nu : ℝ) : ℂ :=
  coefficient u n 1 / complexOrderK (nu : ℂ) (modeFrequency n)

variable {u : ℝ × ℝ → ℂ} {nu Y : ℝ} {n : ℤ}
variable (hu : ContDiffOn ℝ 2 u upperDomain)
  (hp : ∀ x y : ℝ, 0 < y → u (x+1,y)=u(x,y))
  (hnu : 0 ≤ nu)
  (hPDE : ∀ p ∈ upperDomain,
    -(p.2 : ℂ)^2 * (partialX (partialX u) p + partialY (partialY u) p) =
      (1/4 - (nu : ℂ)^2) * u p)
  (hY : 0 < Y)
  (hstrip : Integrable (fun p : PeriodCell × ℝ => p.2⁻¹^2 * ‖u (p.1,p.2)‖^2)
    ((volume : Measure PeriodCell).prod (volume.restrict (Ioi Y))))
  (hn : n ≠ 0)

/-- The actual PDE, periodic integration by parts, square-root change of
variables, and raw strip L2 transport pay all hypotheses of K selection. -/
theorem actualBesselMode_eq_realK (q : ℝ) (hq : 0 < q) :
    actualBesselMode u n q =
      realTailKCoefficient nu 1 (actualBesselMode u n) * complexOrderK (nu : ℂ) q := by
  have hf : TailBesselSolution (nu : ℂ) 0 (actualBesselMode u n) := by
    intro t ht
    exact actual_fourier_bessel_jet hu hp (nu : ℂ) hPDE hn ht
  have hL2 := actual_fourier_log_bessel_memLp_of_strip hu hY hstrip hn
  exact real_tail_L2_solution_eq_K hnu (by norm_num) hf (by norm_num)
    (Real.exp_pos (Real.log (modeFrequency n*Y))).le hL2 q hq

/-- First recover the original coefficient with the explicit native ODE
constant. This still contains no assumed Fourier-shape identity. -/
theorem actual_coefficient_eq_native_realK {y : ℝ} (hy : 0 < y) :
    coefficient u n y = realTailKCoefficient nu 1 (actualBesselMode u n) *
      (Real.sqrt y : ℂ) * complexOrderK (nu : ℂ) (modeFrequency n*y) := by
  have hrec := coefficient_recovery (coefficient u n) (modeFrequency_pos hn) hy
  change coefficient u n y = (Real.sqrt y : ℂ) *
    actualBesselMode u n (modeFrequency n*y) at hrec
  rw [actualBesselMode_eq_realK hu hp hnu hPDE hY hstrip hn _
    (mul_pos (modeFrequency_pos hn) hy)] at hrec
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hrec

/-- The ODE coefficient equals the actual height-one quotient. -/
theorem native_realK_coefficient_eq_value :
    realTailKCoefficient nu 1 (actualBesselMode u n) = realMaassKCoefficient u n nu := by
  have h := actual_coefficient_eq_native_realK hu hp hnu hPDE hY hstrip hn
    (by norm_num : (0 : ℝ) < 1)
  simp only [Real.sqrt_one, Complex.ofReal_one, mul_one] at h
  exact (eq_div_iff (actualRealK_ne_zero nu (modeFrequency_pos hn))).mpr h.symm

/-- Actual nonzero Fourier coefficient formula, including the real
threshold nu=0 and every exceptional real-order parameter. -/
theorem actual_nonzero_coefficient_eq_realK {y : ℝ} (hy : 0 < y) :
    coefficient u n y = realMaassKCoefficient u n nu * (Real.sqrt y : ℂ) *
      complexOrderK (nu : ℂ) (2*Real.pi*|(n : ℝ)|*y) := by
  have h := actual_coefficient_eq_native_realK hu hp hnu hPDE hY hstrip hn hy
  rw [native_realK_coefficient_eq_value hu hp hnu hPDE hY hstrip hn] at h
  exact h

/-- The same constant can be read at any positive height. The value-one
definition therefore introduces no preferred cusp normalization. -/
theorem realMaassKCoefficient_eq_value_at {y : ℝ} (hy : 0 < y) :
    realMaassKCoefficient u n nu = coefficient u n y /
      ((Real.sqrt y : ℂ) * complexOrderK (nu : ℂ) (modeFrequency n*y)) := by
  have hden : (Real.sqrt y : ℂ) * complexOrderK (nu : ℂ) (modeFrequency n*y) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 hy).ne')
      (actualRealK_ne_zero nu (mul_pos (modeFrequency_pos hn) hy))
  apply (eq_div_iff hden).mpr
  have h := actual_nonzero_coefficient_eq_realK hu hp hnu hPDE hY hstrip hn hy
  simpa only [mul_assoc] using h.symm

end
end ImbalancedChen.Part3.ActualRealMaassFourierK20261026a
