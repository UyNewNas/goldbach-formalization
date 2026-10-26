import ImbalancedChen.Part3GammaSmoothCoreMultiplierEnergyLift
import ImbalancedChen.Part3ActualDirichletCauchySchwarz

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The native first-derivative product rule gives a pointwise hyperbolic
energy budget for the original actual modular cutoff. Its constant is
the proved actual cutoffEnergyConstant, uniform in scale Y>1, level and
point. This is the derivative estimate needed for extending the actual
core-to-energy multiplier once its classical gradient is identified.
-/

namespace ImbalancedChen.Part3.GammaActualCutoffNativeGradientBudget20261026b

noncomputable section
open Set Filter
open scoped UpperHalfPlane
open MaassWeakOperatorCore20261024zz Gamma0CompactTensorPoincareC2Core20261025a
open Gamma0CompactGreenProductL120261025a GammaNativeMaassLeibniz20261026a
open ActualPoincareDirichletTrace20261025a ActualDirichletCauchySchwarz20261025a
open ActualModularSmoothCuspCutoff20261025a ActualModularCutoffGradient20261025a
open ActualCuspStripCutoff20261025a
open ActualModularCutoffMaassBudget20261025a Gamma0WeightedCutoffDefectLimit20261026a

/-- The literal squared hyperbolic first-gradient norm. -/
def nativeEnergySq (F : UpperHalfPlane → ℂ) (z : UpperHalfPlane) : ℝ :=
  z.im^2 * (‖nativeDx F z‖^2 + ‖nativeDy F z‖^2)

theorem nativeEnergySq_nonneg (F : UpperHalfPlane → ℂ) (z : UpperHalfPlane) :
    0 ≤ nativeEnergySq F z := by
  unfold nativeEnergySq
  positivity

private theorem complex_add_sq_le (a b : ℂ) :
    ‖a+b‖^2 ≤ 2*(‖a‖^2+‖b‖^2) := by
  calc
    _ ≤ (‖a‖+‖b‖)^2 := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le a b) 2
    _ ≤ _ := by nlinarith [sq_nonneg (‖a‖-‖b‖)]

/-- No independent product-gradient or energy conclusion is supplied:
both coordinate product rules are the literal proved native derivatives. -/
theorem nativeEnergySq_mul_le (chi F : UpperHalfPlane → ℂ)
    (hchi : ContDiffOn ℝ 2 (extendUpper chi) positiveChart)
    (hF : ContDiffOn ℝ 2 (extendUpper F) positiveChart) (z : UpperHalfPlane) :
    nativeEnergySq (chi*F) z ≤
      2*‖chi z‖^2*nativeEnergySq F z + 2*‖F z‖^2*nativeEnergySq chi z := by
  have hx := complex_add_sq_le (nativeDx chi z * F z) (chi z * nativeDx F z)
  have hy := complex_add_sq_le (nativeDy chi z * F z) (chi z * nativeDy F z)
  simp only [norm_mul,mul_pow] at hx hy
  have hsum := add_le_add hx hy
  have hweighted := mul_le_mul_of_nonneg_left hsum (sq_nonneg z.im)
  unfold nativeEnergySq
  rw [nativeDx_mul chi F hchi hF z,nativeDy_mul chi F hchi hF z]
  calc
    _ ≤ z.im^2 *
        (2*(‖nativeDx chi z‖^2*‖F z‖^2+‖chi z‖^2*‖nativeDx F z‖^2) +
         2*(‖nativeDy chi z‖^2*‖F z‖^2+‖chi z‖^2*‖nativeDy F z‖^2)) := hweighted
    _ = _ := by ring

/-- Genuine equality with the actual modular gradient density, proved
using the positive-chart germ of the original zero extension. -/
theorem nativeEnergySq_actualCutoff (Y : ℝ) (z : UpperHalfPlane) :
    nativeEnergySq (complexGlobalH Y) z = cutoffEnergyH Y z := by
  have hg := extendGlobal_germ Y z.im_pos
  unfold nativeEnergySq nativeDx nativeDy
  rw [sliceDx_eq_of_eventuallyEq hg,sliceDy_eq_of_eventuallyEq hg]
  rw [cutoffEnergyH,hyperbolicChartDirichlet_self_re_eq]
  simp only [chartEnergySq,Complex.normSq_eq_norm_sq]

theorem actualCutoff_norm_le_one (Y : ℝ) (hY : 1 ≤ Y) (z : UpperHalfPlane) :
    ‖complexGlobalH Y z‖ ≤ 1 := by
  have hb := globalCutoff_bounds Y hY z
  simpa only [complexGlobalH,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hb.1] using hb.2

/-- Uniform actual cutoff product energy. There is no high-cusp volume
factor and no boundedness assumption on F: the error is its true mass. -/
theorem nativeEnergySq_actualCutoff_mul_le (Y : ℝ) (hY : 1 < Y)
    (F : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ 2 (extendUpper F) positiveChart) (z : UpperHalfPlane) :
    nativeEnergySq (complexGlobalH Y * F) z ≤
      2*nativeEnergySq F z + 2*cutoffEnergyConstant*‖F z‖^2 := by
  have hp := nativeEnergySq_mul_le (complexGlobalH Y) F
    (extendGlobal_C2 Y (lt_trans (by norm_num) hY)) hF z
  have hs : ‖complexGlobalH Y z‖^2 ≤ 1 := by
    have hn := actualCutoff_norm_le_one Y hY.le z
    nlinarith [norm_nonneg (complexGlobalH Y z)]
  have he : nativeEnergySq (complexGlobalH Y) z ≤ cutoffEnergyConstant := by
    rw [nativeEnergySq_actualCutoff]
    exact cutoffEnergyH_uniform Y hY z
  have hfirst : 2*‖complexGlobalH Y z‖^2*nativeEnergySq F z ≤ 2*nativeEnergySq F z := by
    have hh := mul_le_mul_of_nonneg_right hs (nativeEnergySq_nonneg F z)
    nlinarith
  have hsecond : 2*‖F z‖^2*nativeEnergySq (complexGlobalH Y) z ≤
      2*cutoffEnergyConstant*‖F z‖^2 := by
    have hh := mul_le_mul_of_nonneg_left he (sq_nonneg ‖F z‖)
    nlinarith
  exact hp.trans (add_le_add hfirst hsecond)

end
end ImbalancedChen.Part3.GammaActualCutoffNativeGradientBudget20261026b
