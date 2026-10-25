import ImbalancedChen.Part3ComplexBesselAbelBasis
import ImbalancedChen.Part3ComplexOrderKQODE
import ImbalancedChen.Part3GeneralISmallQWronskian
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-!
# Actual K belongs to the actual I_nu, I_-nu basis on the open strip

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

Every ODE and differentiability obligation is discharged by the actual
K integral and the actual Gamma-coefficient I series. The genuine I-pair
Wronskian is nonzero when 0<Re nu<1. Thus explicit coefficients, computed
from actual function values and derivatives at q=1, represent actual K
on every q>0. Their identification as +/-pi/(2 sin(pi nu)) is a remaining
small-q calculation, and is not assumed or asserted here.
-/

namespace ImbalancedChen.Part3.ActualComplexKIBasis

noncomputable section
open ComplexBesselAbelBasis ComplexOrderKBridgeSourceOnly ComplexOrderKQCalculus
open ComplexOrderKQODE GeneralComplexISeriesSourceOnly GeneralIQODE20261025a
open GeneralISmallQWronskian20261025a

theorem sin_pi_order_ne_zero {ν : ℂ} (hL : 0 < ν.re) (hU : ν.re < 1) :
    Complex.sin ((Real.pi : ℂ) * ν) ≠ 0 := by
  intro hz
  obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp hz
  have hr : Real.pi * ν.re = (k : ℝ) * Real.pi := by
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.intCast_re, Complex.intCast_im, mul_zero, sub_zero] using congrArg Complex.re hk
  have hkν : (k : ℝ) = ν.re := by
    apply mul_left_cancel₀ Real.pi_ne_zero
    simpa only [mul_comm] using hr.symm
  have hk0 : (0 : ℤ) < k := by exact_mod_cast (show (0 : ℝ) < k by rw [hkν]; exact hL)
  have hk1 : k < (1 : ℤ) := by exact_mod_cast (show (k : ℝ) < 1 by rw [hkν]; exact hU)
  omega

theorem actualK_positiveBesselSolution (ν : ℂ) :
    PositiveBesselSolution ν (complexOrderK ν) := by
  intro q hq
  exact ⟨(complexOrderK_hasDerivAt_q ν hq).differentiableAt.hasDerivAt,
    (deriv_complexOrderK_hasDerivAt_q ν hq).differentiableAt.hasDerivAt,
    complexOrderK_modifiedBessel_equation ν hq⟩

theorem actualI_positiveBesselSolution {ν : ℂ} (hν : -1 < ν.re) :
    PositiveBesselSolution ν (generalI ν) := by
  intro q hq
  exact ⟨(generalI_hasDerivAt hν hq).differentiableAt.hasDerivAt,
    (deriv_generalI_hasDerivAt hν hq).differentiableAt.hasDerivAt,
    generalI_modifiedBessel_equation hν hq⟩

theorem actualI_negative_positiveBesselSolution {ν : ℂ} (hν : ν.re < 1) :
    PositiveBesselSolution ν (generalI (-ν)) := by
  have hn : -1 < (-ν).re := by simpa only [Complex.neg_re] using (neg_lt_neg hν)
  intro q hq
  obtain ⟨h₁, h₂, hODE⟩ := actualI_positiveBesselSolution hn q hq
  exact ⟨h₁, h₂, by simpa only [neg_sq] using hODE⟩

theorem actualI_pair_weightedWronskian_ne_zero {ν : ℂ}
    (hL : 0 < ν.re) (hU : ν.re < 1) :
    weightedWronskian (generalI ν) (generalI (-ν)) 1 ≠ 0 := by
  have hW := q_mul_generalIWronskian_eq_neg_two_sin
    (by linarith only [hL] : -1 < ν.re) hU (q := 1) (by norm_num)
  change weightedWronskian (generalI ν) (generalI (-ν)) 1 =
    -2 * Complex.sin ((Real.pi : ℂ) * ν) / (Real.pi : ℂ) at hW
  rw [hW]
  exact div_ne_zero (mul_ne_zero (by norm_num) (sin_pi_order_ne_zero hL hU))
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)

def actualKICoefficientPlus (ν : ℂ) : ℂ :=
  weightedWronskian (complexOrderK ν) (generalI (-ν)) 1 /
    weightedWronskian (generalI ν) (generalI (-ν)) 1

def actualKICoefficientMinus (ν : ℂ) : ℂ :=
  weightedWronskian (generalI ν) (complexOrderK ν) 1 /
    weightedWronskian (generalI ν) (generalI (-ν)) 1

/-- Genuine global basis representation of the literal actual K integral.
Only the geometric strip and positive q are hypotheses. -/
theorem actualK_eq_generalI_basis {ν : ℂ} (hL : 0 < ν.re) (hU : ν.re < 1)
    {q : ℝ} (hq : 0 < q) :
    complexOrderK ν q = actualKICoefficientPlus ν * generalI ν q +
      actualKICoefficientMinus ν * generalI (-ν) q := by
  exact solution_eq_basis_at_one
    (actualI_positiveBesselSolution (by linarith only [hL]))
    (actualI_negative_positiveBesselSolution hU) (actualK_positiveBesselSolution ν)
    (actualI_pair_weightedWronskian_ne_zero hL hU) hq

end

end ImbalancedChen.Part3.ActualComplexKIBasis
