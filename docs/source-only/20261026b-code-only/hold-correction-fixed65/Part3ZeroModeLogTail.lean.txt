import ImbalancedChen.Part3RadialSmoothCoreDerivativeClosure
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

Scalar compact smooth half-line calculation with the actual endpoint trace.
This is a tail calculation in log height, not a spectral gap on a quotient.
-/

namespace ImbalancedChen.Part3.ZeroModeLogTail20261026b
noncomputable section
open MeasureTheory Set
open RadialSchrodingerL2Form20261025a

def tailMass (R : ℝ) (F : ℝ → ℂ) : ℝ := ∫ r in Ioi R, ‖F r‖ ^ 2
def tailDerivativeEnergy (R : ℝ) (F : ℝ → ℂ) : ℝ :=
  ∫ r in Ioi R, ‖deriv F r‖ ^ 2
def tailShearEnergy (R : ℝ) (F : ℝ → ℂ) : ℝ :=
  ∫ r in Ioi R, ‖deriv F r + (1 / 2 : ℂ) * F r‖ ^ 2

theorem compact_tail_cross (R : ℝ) (T : RadialTest) :
    2 * (∫ r in Ioi R, (star (T.function r) * deriv T.function r).re) =
      - ‖T.function R‖ ^ 2 := by
  let q : ℝ → ℂ := fun r => star (T.function r) * T.function r
  have hq : ContDiff ℝ 1 q :=
    (T.smooth.of_le (by simp)).star.mul (T.smooth.of_le (by simp))
  have hqc : HasCompactSupport q := T.compact.mul_left
  have hd (r : ℝ) : deriv q r =
      star (deriv T.function r) * T.function r +
        star (T.function r) * deriv T.function r := by
    exact (((T.smooth.differentiable (by simp) r).hasDerivAt.star).mul
      ((T.smooth.differentiable (by simp) r).hasDerivAt)).deriv
  have hiA : IntegrableOn (fun r => star (deriv T.function r) * T.function r) (Ioi R) :=
    (T.derivative_continuous.star.mul T.smooth.continuous).
      integrable_of_hasCompactSupport T.compact.mul_left |>.integrableOn
  have hiB : IntegrableOn (fun r => star (T.function r) * deriv T.function r) (Ioi R) :=
    (T.smooth.continuous.star.mul T.derivative_continuous).
      integrable_of_hasCompactSupport T.compact.deriv.mul_left |>.integrableOn
  have h := HasCompactSupport.integral_Ioi_deriv_eq hq hqc R
  simp_rw [hd] at h
  rw [integral_add hiA hiB] at h
  have hre := congrArg Complex.re h
  rw [Complex.add_re, Complex.neg_re, ← integral_re hiA,
    ← integral_re hiB] at hre
  have heq (r : ℝ) :
      (star (deriv T.function r) * T.function r).re =
        (star (T.function r) * deriv T.function r).re := by
    simp [Complex.mul_re, Complex.star_def]
    ring
  have hnorm : (q R).re = ‖T.function R‖ ^ 2 := by
    simp [q, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      Complex.mul_re, Complex.star_def]
  simp_rw [heq] at hre
  rw [hnorm] at hre
  linarith

/-- The mixed term is the negative lower endpoint trace. -/
theorem compact_tail_shear_identity (R : ℝ) (T : RadialTest) :
    tailShearEnergy R T.function =
      tailDerivativeEnergy R T.function + (1 / 4 : ℝ) * tailMass R T.function -
        ‖T.function R‖ ^ 2 / 2 := by
  have hiD : IntegrableOn (fun r => ‖deriv T.function r‖ ^ 2) (Ioi R) :=
    ((memLp_two_iff_integrable_sq_norm T.derivative_memLp.aestronglyMeasurable).mp
      T.derivative_memLp).integrableOn
  have hiM : IntegrableOn (fun r => ‖T.function r‖ ^ 2) (Ioi R) :=
    ((memLp_two_iff_integrable_sq_norm T.function_memLp.aestronglyMeasurable).mp
      T.function_memLp).integrableOn
  have hiC : IntegrableOn
      (fun r => (star (T.function r) * deriv T.function r).re) (Ioi R) :=
    ((T.smooth.continuous.star.mul T.derivative_continuous).
      integrable_of_hasCompactSupport T.compact.deriv.mul_left).re.integrableOn
  have hp (r : ℝ) :
      ‖deriv T.function r + (1 / 2 : ℂ) * T.function r‖ ^ 2 =
        ‖deriv T.function r‖ ^ 2 +
          (1 / 4 : ℝ) * ‖T.function r‖ ^ 2 +
          (star (T.function r) * deriv T.function r).re := by
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.star_def, Complex.conj_re, Complex.conj_im]
    norm_num
    ring
  unfold tailShearEnergy tailDerivativeEnergy tailMass
  simp_rw [hp]
  rw [integral_add (hiD.add hiM.const_mul) hiC,
    integral_add hiD hiM.const_mul, integral_const_mul]
  have hc := compact_tail_cross R T
  linarith

theorem compact_tail_hardy (R : ℝ) (T : RadialTest) :
    (1 / 4 : ℝ) * tailMass R T.function - ‖T.function R‖ ^ 2 / 2 ≤
      tailShearEnergy R T.function := by
  have h := compact_tail_shear_identity R T
  have hn : 0 ≤ tailDerivativeEnergy R T.function :=
    integral_nonneg (fun _ => sq_nonneg _)
  linarith

/-- A quantitative endpoint estimate, proved rather than postulated. -/
theorem compact_tail_trace_bound (R : ℝ) (T : RadialTest) :
    ‖T.function R‖ ^ 2 ≤ tailMass R T.function + tailDerivativeEnergy R T.function := by
  have hiD : IntegrableOn (fun r => ‖deriv T.function r‖ ^ 2) (Ioi R) :=
    ((memLp_two_iff_integrable_sq_norm T.derivative_memLp.aestronglyMeasurable).mp
      T.derivative_memLp).integrableOn
  have hiM : IntegrableOn (fun r => ‖T.function r‖ ^ 2) (Ioi R) :=
    ((memLp_two_iff_integrable_sq_norm T.function_memLp.aestronglyMeasurable).mp
      T.function_memLp).integrableOn
  have hiC : IntegrableOn
      (fun r => (star (T.function r) * deriv T.function r).re) (Ioi R) :=
    ((T.smooth.continuous.star.mul T.derivative_continuous).
      integrable_of_hasCompactSupport T.compact.deriv.mul_left).re.integrableOn
  have hpoint (r : ℝ) :
      -(2 * (star (T.function r) * deriv T.function r).re) ≤
        ‖T.function r‖ ^ 2 + ‖deriv T.function r‖ ^ 2 := by
    have hn := sq_nonneg ‖deriv T.function r + T.function r‖
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.star_def, Complex.conj_re, Complex.conj_im] at *
    nlinarith
  have h := integral_mono (hiC.const_mul (-2)) (hiM.add hiD) hpoint
  rw [integral_const_mul, integral_add hiM hiD] at h
  have hc := compact_tail_cross R T
  unfold tailMass tailDerivativeEnergy
  linarith

end
end ImbalancedChen.Part3.ZeroModeLogTail20261026b
