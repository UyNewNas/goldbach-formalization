import ImbalancedChen.Part3ComplexCompactGreenGluing
import ImbalancedChen.Part3ComplexOrderKRadialRegularity
import ImbalancedChen.Part3GeneralIKWronskian
import ImbalancedChen.Part3ActualKRadialLogConjugation

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
General complex-order actual Bessel Green kernel for 0<Re nu<1. Both
functions are literal supplied I-series/K-integral definitions. Their ODEs,
C2 regularity, and normalized Wronskian are derived in imported modules,
not premises. The resulting weak identity is for arbitrary complex compact
C2 tests. This is not a spectral resolution or Kuznetsov supplier.
-/
namespace ImbalancedChen.Part3.GeneralActualRadialGreenSourceOnly
noncomputable section
open Set MeasureTheory
open scoped Topology
open GeneralComplexISeriesSourceOnly GeneralIQODE20261025a
open ComplexOrderKBridgeSourceOnly ComplexOrderKQCalculus ComplexOrderKQODE
open ComplexOrderKRadialRegularitySourceOnly GeneralIKWronskianSourceOnly
open ComplexCompactGreenGluingSourceOnly ActualKRadialLogConjugation20261025a

def radialI (nu : ℂ) (r : ℝ) : ℂ := generalI nu (Real.exp r)
def potential (nu : ℂ) (r : ℝ) : ℂ := (Real.exp (2 * r) : ℂ) + nu ^ 2

theorem radialI_C2 {nu : ℂ} (hnu : -1 < nu.re) : ContDiff ℝ 2 (radialI nu) := by
  exact (generalI_contDiffOn_two hnu).comp_contDiff Real.contDiff_exp
    (fun r => Real.exp_pos r)

theorem radialI_hasDerivAt {nu : ℂ} (hnu : -1 < nu.re) (r : ℝ) :
    HasDerivAt (radialI nu) (Real.exp r • deriv (generalI nu) (Real.exp r)) r := by
  exact (generalI_differentiableAt hnu (Real.exp_pos r)).hasDerivAt.scomp r
    (Real.hasDerivAt_exp r)

private theorem exp_two_cast (r : ℝ) :
    (Real.exp (2 * r) : ℂ) = (Real.exp r : ℂ) ^ 2 := by
  rw [show 2 * r = r + r by ring, Real.exp_add]
  push_cast
  ring

theorem actual_radialI_homogeneous {nu : ℂ} (hnu : -1 < nu.re) (r : ℝ) :
    operator (potential nu) (radialI nu) r = 0 := by
  have hf : DifferentiableOn ℝ (generalI nu) (Ioi (0 : ℝ)) := by
    intro q hq
    exact (generalI_differentiableAt hnu hq).differentiableWithinAt
  have hd : DifferentiableOn ℝ (deriv (generalI nu)) (Ioi (0 : ℝ)) := by
    intro q hq
    exact (generalI_deriv_differentiableAt hnu hq).differentiableWithinAt
  change operator (potential nu) (logPull (generalI nu)) r = 0
  unfold operator
  rw [logPull_second_deriv _ hf hd]
  simp only [potential, logPull, Complex.real_smul, Complex.ofReal_pow, exp_two_cast]
  have h := generalI_modifiedBessel_equation hnu (Real.exp_pos r)
  linear_combination -h

theorem actual_radialK_homogeneous (nu : ℂ) (r : ℝ) :
    operator (potential nu) (radialK nu) r = 0 := by
  unfold operator
  rw [radialK_second_deriv]
  simp only [potential, radialK, radialMoment, Complex.real_smul,
    Complex.ofReal_pow, exp_two_cast]
  have h := complexOrderK_qMoment_ODE nu (Real.exp_pos r)
  linear_combination -h

/-- Positive source normalization for -d²/dr²+exp(2r)+nu². -/
theorem actual_radial_source_wronskian {nu : ℂ}
    (hnu : 0 < nu.re) (hnuUpper : nu.re < 1) (s : ℝ) :
    deriv (radialI nu) s * radialK nu s - radialI nu s * deriv (radialK nu) s = 1 := by
  have hi : -1 < nu.re := by linarith
  rw [(radialI_hasDerivAt hi s).deriv, (radialK_hasDerivAt nu s).deriv]
  have hk := (complexOrderK_hasDerivAt_q nu (Real.exp_pos s)).deriv
  simp only [radialI, radialK, radialMoment, Complex.real_smul]
  rw [← hk]
  have hw := q_actualIKWronskian_eq_neg_one hnu hnuUpper (Real.exp_pos s)
  unfold actualIKWronskian at hw
  linear_combination -hw

/-- The actual general-order min/max Green kernel on the logarithmic line. -/
def actualRadialGreen (nu : ℂ) (s r : ℝ) : ℂ :=
  kernel (radialI nu) (radialK nu) s r

theorem actualRadialGreen_continuous {nu : ℂ} (hnu : -1 < nu.re) (s : ℝ) :
    Continuous (actualRadialGreen nu s) := by
  exact ((radialI_C2 hnu).continuous.comp (continuous_id.min continuous_const)).mul
    ((radialK_C2 nu).continuous.comp (continuous_id.max continuous_const))

/-- The actual normalized Green identity. No differential equation,
Wronskian, boundary flux, or connection formula is a hypothesis. -/
theorem actualRadialGreen_weak_identity {nu : ℂ}
    (hnu : 0 < nu.re) (hnuUpper : nu.re < 1) (s : ℝ) (phi : ℝ → ℂ)
    (hphi : ContDiff ℝ 2 phi) (hc : HasCompactSupport phi) :
    (∫ r : ℝ, actualRadialGreen nu s r *
      (-deriv (deriv phi) r + ((Real.exp (2 * r) : ℂ) + nu ^ 2) * phi r)) = phi s := by
  have hi : -1 < nu.re := by linarith
  have h := compact_green_residual_identity (radialI nu) (radialK nu)
    (potential nu) phi s (radialI_C2 hi) (radialK_C2 nu) hphi hc
  have he (r : ℝ) : splice s
      (fun x => radialK nu s * operator (potential nu) (radialI nu) x * phi x)
      (fun x => radialI nu s * operator (potential nu) (radialK nu) x * phi x) r = 0 := by
    simp only [splice, actual_radialI_homogeneous hi, actual_radialK_homogeneous,
      mul_zero, zero_mul, ite_self]
  simp only [he, sub_zero, actual_radial_source_wronskian hnu hnuUpper, one_mul] at h
  exact h

end
end ImbalancedChen.Part3.GeneralActualRadialGreenSourceOnly
