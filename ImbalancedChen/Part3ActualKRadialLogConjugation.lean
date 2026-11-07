import ImbalancedChen.Part3PositiveMellinL2
import ImbalancedChen.Part3ImaginaryOrderKSecondQDerivative
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
Liouville conjugation for the actual K radial differential expression.
The dq/q measure and its complex L2 logarithmic isometry already exist in
Part3PositiveMultiplicativeLog and Part3PositiveMellinL2; they are reused.
This module supplies the missing differential intertwining, including the
actual K_{2it} mode and the actual compact native spectral test.
No self-adjoint realization or KL spectral normalization is asserted.
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
-/

namespace ImbalancedChen.Part3.ActualKRadialLogConjugation20261025a

noncomputable section
open Set Filter
open ImaginaryOrderKBesselSourceOnly
open ImaginaryOrderKQDerivativeSourceOnly
open ImaginaryOrderKSecondQDerivativeSourceOnly
open PositiveMellinL2SourceOnly
open P3ActualLiteralPacketIntegralSourceOnly
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest spectralTest_contDiff)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The pointwise representative of the existing logarithmic L2 chart. -/
def logPull (F : ℝ → E) (r : ℝ) : E := F (Real.exp r)

/-- The physical radial expression -(q d/dq)^2 + q^2. -/
def qRadialOperator (F : ℝ → E) (q : ℝ) : E :=
  -(q ^ 2 • deriv (deriv F) q + q • deriv F q) + q ^ 2 • F q

/-- The real-line Schrödinger expression with its literal exponential
potential. No quarter-threshold from the dy/y^2 cusp coordinate occurs. -/
def logSchrodinger (G : ℝ → E) (r : ℝ) : E :=
  -deriv (deriv G) r + Real.exp (2 * r) • G r

theorem logPull_hasDerivAt (F : ℝ → E)
    (hF : DifferentiableOn ℝ F (Ioi (0 : ℝ))) (r : ℝ) :
    HasDerivAt (logPull F) (Real.exp r • deriv F (Real.exp r)) r := by
  have hq : DifferentiableAt ℝ F (Real.exp r) :=
    (hF _ (Real.exp_pos r)).differentiableAt (Ioi_mem_nhds (Real.exp_pos r))
  simpa only [logPull, Function.comp_def] using
    hq.hasDerivAt.scomp r (Real.hasDerivAt_exp r)

/-- Exact second derivative in logarithmic physical coordinate. The
first-derivative term is retained with its actual coefficient q. -/
theorem logPull_second_deriv (F : ℝ → E)
    (hF : DifferentiableOn ℝ F (Ioi (0 : ℝ)))
    (hD : DifferentiableOn ℝ (deriv F) (Ioi (0 : ℝ))) (r : ℝ) :
    deriv (deriv (logPull F)) r =
      (Real.exp r) ^ 2 • deriv (deriv F) (Real.exp r) +
        Real.exp r • deriv F (Real.exp r) := by
  have hfirst : deriv (logPull F) =
      fun u => Real.exp u • deriv F (Real.exp u) := by
    funext u
    exact (logPull_hasDerivAt F hF u).deriv
  rw [hfirst]
  have hq : DifferentiableAt ℝ (deriv F) (Real.exp r) :=
    (hD _ (Real.exp_pos r)).differentiableAt (Ioi_mem_nhds (Real.exp_pos r))
  have hd := (Real.hasDerivAt_exp r).smul
    (hq.hasDerivAt.scomp r (Real.hasDerivAt_exp r))
  simpa only [Function.comp_def, Pi.smul_apply, smul_smul, pow_two] using hd.deriv

/-- The expanded physical expression is the literal square of the Euler
operator, rather than a separately assumed differential operator. -/
theorem qRadialOperator_eq_euler_square (F : ℝ → E)
    {q : ℝ} (hD : DifferentiableAt ℝ (deriv F) q) :
    qRadialOperator F q =
      -(q • deriv (fun x : ℝ => x • deriv F x) q) + q ^ 2 • F q := by
  have hd := (hasDerivAt_id q).smul hD.hasDerivAt
  rw [hd.deriv]
  simp only [qRadialOperator, Pi.smul_apply, id_eq, one_smul,
    smul_add, smul_smul, pow_two]
/-- Differential intertwining in the exact coordinate of the already
constructed L2(dq/q) to L2(dr) isometry. -/
theorem radial_log_conjugation (F : ℝ → E)
    (hF : DifferentiableOn ℝ F (Ioi (0 : ℝ)))
    (hD : DifferentiableOn ℝ (deriv F) (Ioi (0 : ℝ))) (r : ℝ) :
    logPull (qRadialOperator F) r = logSchrodinger (logPull F) r := by
  have hexp : Real.exp (2 * r) = (Real.exp r) ^ 2 := by
    rw [show 2 * r = r + r by ring, Real.exp_add, pow_two]
  unfold qRadialOperator logSchrodinger
  rw [logPull_second_deriv F hF hD r, hexp]
  rfl

/-- The physical radial eigenvalue follows from the actual integral ODE,
with imaginary order 2it giving precisely 4t^2. -/
theorem actualK_radial_eigen (t : ℝ) {q : ℝ} (hq : 0 < q) :
    qRadialOperator (imaginaryOrderK t) q =
      4 * t ^ 2 * imaginaryOrderK t q := by
  have h := actual_K_modifiedBessel_equation t hq
  unfold qRadialOperator
  simp only [smul_eq_mul]
  linear_combination -h

private theorem actualK_deriv_differentiableOn (t : ℝ) :
    DifferentiableOn ℝ (deriv (imaginaryOrderK t)) (Ioi (0 : ℝ)) := by
  intro q hq
  exact (deriv_imaginaryOrderK_hasDerivAt_qSecond t hq).differentiableAt.differentiableWithinAt

/-- The actual integral K_{2it}(exp r) is a generalized eigenfunction of
-d^2/dr^2+exp(2r). No L2 or orthogonality statement is assumed. -/
theorem actualK_logSchrodinger_eigen (t r : ℝ) :
    logSchrodinger (logPull (imaginaryOrderK t)) r =
      4 * t ^ 2 * logPull (imaginaryOrderK t) r := by
  rw [← radial_log_conjugation (imaginaryOrderK t)
    (imaginaryOrderK_differentiableOn_q t) (actualK_deriv_differentiableOn t) r]
  exact actualK_radial_eigen t (Real.exp_pos r)

/-- The equivalent ordinary real-coordinate second-order equation. -/
theorem actualK_log_second_equation (t r : ℝ) :
    deriv (deriv (logPull (imaginaryOrderK t))) r =
      (Real.exp (2 * r) - 4 * t ^ 2) * logPull (imaginaryOrderK t) r := by
  have h := actualK_logSchrodinger_eigen t r
  unfold logSchrodinger at h
  simp only [smul_eq_mul] at h
  linear_combination -h

/-- The existing actual compact spectral test satisfies the same
intertwining with all local smoothness hypotheses discharged. -/
theorem actual_native_test_conjugation {ι : Type*} (P : PacketData ι)
    (k : D4 → ℤ) (r : ℝ) :
    qRadialOperator (spectralTest k P.Y0) (Real.exp r) =
      logSchrodinger (actualSpectralLogProfile P k) r := by
  have htwo : ContDiff ℝ 2 (spectralTest k P.Y0) :=
    (spectralTest_contDiff k P.Y0).of_le (by norm_num)
  exact radial_log_conjugation (spectralTest k P.Y0)
    (htwo.differentiable (by norm_num)).differentiableOn
    htwo.differentiable_deriv_two.differentiableOn r

/-- The native compact test's literal physical radial quadratic form
becomes the exponential-potential energy on the real log axis. The actual
Jacobian theorem supplies the measure transport; no integral identity is
assumed as an input. -/
theorem actual_native_radial_energy_log {ι : Type*} (P : PacketData ι)
    (k : D4 → ℤ) :
    (∫ q : ℝ,
      (‖q • deriv (spectralTest k P.Y0) q‖ ^ 2 +
        q ^ 2 * ‖spectralTest k P.Y0 q‖ ^ 2)
      ∂PositiveMultiplicativeLogSourceOnly.positiveMultiplicativeMeasure) =
      ∫ r : ℝ,
        ‖deriv (actualSpectralLogProfile P k) r‖ ^ 2 +
          Real.exp (2 * r) * ‖actualSpectralLogProfile P k r‖ ^ 2 := by
  have htwo : ContDiff ℝ 2 (spectralTest k P.Y0) :=
    (spectralTest_contDiff k P.Y0).of_le (by norm_num)
  have hc : Continuous (spectralTest k P.Y0) := htwo.continuous
  have hd : Continuous (deriv (spectralTest k P.Y0)) :=
    htwo.continuous_deriv (by norm_num)
  have hm : Measurable (fun q : ℝ =>
      ‖q • deriv (spectralTest k P.Y0) q‖ ^ 2 +
        q ^ 2 * ‖spectralTest k P.Y0 q‖ ^ 2) :=
    (((continuous_id.smul hd).norm.pow 2).add
      ((continuous_id.pow 2).mul (hc.norm.pow 2))).measurable
  rw [← PositiveMultiplicativeLogSourceOnly.map_exp_volume,
    MeasureTheory.integral_map (by fun_prop) hm.aestronglyMeasurable]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with r
  have hderiv : deriv (actualSpectralLogProfile P k) r =
      Real.exp r • deriv (spectralTest k P.Y0) (Real.exp r) :=
    (logPull_hasDerivAt (spectralTest k P.Y0)
      (htwo.differentiable (by norm_num)).differentiableOn r).deriv
  rw [hderiv, show Real.exp (2 * r) = (Real.exp r) ^ 2 by
    rw [show 2 * r = r + r by ring, Real.exp_add, pow_two]]
  rfl
end
end ImbalancedChen.Part3.ActualKRadialLogConjugation20261025a