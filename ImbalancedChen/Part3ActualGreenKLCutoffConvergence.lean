import ImbalancedChen.Part3ActualGreenKLTransform
import ImbalancedChen.Part3ActualGreenL2IntegralInverse
import ImbalancedChen.Part3RadialWeightedSmoothCutoffDensity
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
The same explicit smooth compact cutoffs of actual Green forcing converge
physically in L2 to the actual Green inverse, while their literal K_i*tau
integrals converge pointwise to the actual resolvent multiplier. The
dominating function is the proved integrable actual Green/K product.
No extended KL map, norm identity, or Plancherel premise is used.
-/
namespace ImbalancedChen.Part3.ActualGreenKLCutoffConvergence20261025a
noncomputable section
open Set MeasureTheory Filter Topology
open RadialSchrodingerL2Form20261025a RadialWeightedCutoffDensity20261025a
open ActualGreenCompactForcing20261025a ActualGreenForcingRegularity20261025a
open ActualGreenForcingEnergy20261025a ActualGreenSmoothFormInverse20261025a
open ActualGreenL2IntegralInverse20261025a ActualGreenKLTransform20261025a
open ActualKLCompactTestIntegrationByParts20261025a ComplexOrderKRadialRegularitySourceOnly

/-- Actual compact smooth tests, built from the literal Green convolution
and the already constructed symmetric bump cutoff. -/
def greenCutoffTest (kappa : ℝ) (hkappa : 0 < kappa) (hkappaUpper : kappa < 1)
    (F : RadialTest) (n : ℕ) : RadialTest :=
  cutoffTest (greenForcing (kappa : ℂ) F.function)
    (greenForcing_smooth (by simpa using hkappa) (by simpa using hkappaUpper)
      F.smooth F.compact) n

theorem greenCutoffTest_function (kappa : ℝ) (hkappa : 0 < kappa)
    (hkappaUpper : kappa < 1) (F : RadialTest) (n : ℕ) (r : ℝ) :
    (greenCutoffTest kappa hkappa hkappaUpper F n).function r =
      cutoff n r • greenForcing (kappa : ℂ) F.function r := rfl

/-- Convergence in the actual physical L2 space, with the limit identified
as the literal Green integral operator, not an abstract chosen inverse. -/
theorem greenCutoffTest_physical_tendsto (kappa : ℝ) (hkappa : 0 < kappa)
    (hkappaUpper : kappa < 1) (F : RadialTest) :
    Tendsto (fun n => radialCoreL2 (greenCutoffTest kappa hkappa hkappaUpper F n))
      atTop (𝓝 (actualGreenL2Operator kappa hkappa hkappaUpper (radialCoreL2 F))) := by
  let hU := greenForcing_memLp_two hkappa hkappaUpper F.smooth.continuous F.compact
  have he : hU.toLp (greenForcing (kappa : ℂ) F.function) =
      actualGreenL2Operator kappa hkappa hkappaUpper (radialCoreL2 F) := by
    rw [actualGreenL2Operator_eq_form_inverse hkappa hkappaUpper]
    apply Lp.ext
    exact hU.coeFn_toLp.trans (actualGreen_eq_form_inverse_smooth hkappa hkappaUpper F)
  have h := cutoffTest_coreL2_tendsto (greenForcing (kappa : ℂ) F.function)
    (greenForcing_smooth (by simpa using hkappa) (by simpa using hkappaUpper)
      F.smooth F.compact) hU
  rw [he] at h
  exact h

/-- Literal integral convergence for every nonzero real spectral
parameter, proved by dominated convergence against the actual U*K product. -/
theorem greenCutoffTest_transform_tendsto (kappa : ℝ) (hkappa : 0 < kappa)
    (hkappaUpper : kappa < 1) (F : RadialTest) (tau : ℝ) (htau : tau ≠ 0) :
    Tendsto (fun n => actualKtransform
      (greenCutoffTest kappa hkappa hkappaUpper F n).function tau) atTop
      (𝓝 (actualKtransform (greenForcing (kappa : ℂ) F.function) tau)) := by
  let U := greenForcing (kappa : ℂ) F.function
  let K := radialK ((tau : ℂ)*Complex.I)
  have hUK : Integrable (fun r : ℝ => U r*K r) :=
    actualKtransform_greenForcing_integrable hkappa hkappaUpper
      F.smooth.continuous F.compact tau htau
  apply tendsto_integral_of_dominated_convergence (fun r : ℝ => ‖U r*K r‖)
  · intro n
    exact ((greenCutoffTest kappa hkappa hkappaUpper F n).smooth.continuous.mul
      (radialK_C2 _).continuous).aestronglyMeasurable
  · exact hUK.norm
  · intro n
    apply Eventually.of_forall
    intro r
    change ‖(cutoff n r • U r)*K r‖ ≤ ‖U r*K r‖
    rw [smul_mul_assoc, norm_smul, Real.norm_of_nonneg (cutoff_range n r).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (cutoff_range n r).2
  · apply Eventually.of_forall
    intro r
    have h := ((tendsto_cutoff r).smul (tendsto_const_nhds (x := U r))).mul
      (tendsto_const_nhds (x := K r))
    simpa only [greenCutoffTest_function, one_smul] using h

/-- The two convergence statements use exactly the same compact tests.
This is the concrete supplier needed to identify a separately constructed
KL extension on a noncompact Green output. -/
theorem greenCutoffTest_transform_resolvent_limit (kappa : ℝ) (hkappa : 0 < kappa)
    (hkappaUpper : kappa < 1) (F : RadialTest) (tau : ℝ) (htau : tau ≠ 0) :
    Tendsto (fun n => actualKtransform
      (greenCutoffTest kappa hkappa hkappaUpper F n).function tau) atTop
      (𝓝 (actualKtransform F.function tau / ((kappa : ℂ)^2+(tau : ℂ)^2))) := by
  have h := greenCutoffTest_transform_tendsto kappa hkappa hkappaUpper F tau htau
  rw [actualKtransform_greenForcing hkappa hkappaUpper F.smooth.continuous F.compact tau htau] at h
  exact h

end
end ImbalancedChen.Part3.ActualGreenKLCutoffConvergence20261025a
