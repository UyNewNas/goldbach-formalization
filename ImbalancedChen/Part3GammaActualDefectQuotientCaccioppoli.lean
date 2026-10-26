import ImbalancedChen.Part3GammaActualNestedDefectEnergyTests
import ImbalancedChen.Part3GammaActualClosedFormIMS
import ImbalancedChen.Part3NestedCutoffDerivativeError

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Actual quotient Caccioppoli for an arbitrary native minimal-adjoint
defect. The nonsmooth cutoff-square test, completed IMS and nested
derivative-error localization are proved suppliers. No H1, equation,
form-test, IMS, mass/error bound or defect-vanishing premise is assumed.
-/

namespace ImbalancedChen.Part3.GammaActualDefectQuotientCaccioppoli20261026b
noncomputable section
open Set Filter MeasureTheory
open scoped UpperHalfPlane
open Gamma0QuotientCellPushforward20261025a Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualMinimalShiftRange20261025a Gamma0ActualEnergyCompletion20261025a
open GammaActualDefectSupportedFormTesting20261026b GammaActualNestedDefectEnergyTests20261026b
open GammaActualQuotientCutoffMultiplier20261026b GammaActualClosedFormCutoffMultiplier20261026b
open GammaActualClosedFormIMS20261026b GammaActualCutoffErrorQuadratic20261026b
open ActualModularSmoothCuspCutoff20261025a ActualModularSmoothCutoffL2Tail20261025a
open ActualModularCutoffGradient20261025a ActualModularCutoffEnergyBudget20261025a
open ActualDirichletCauchySchwarz20261025a Gamma0CompactGreenProductL120261025a
open Gamma0CompactTensorPoincareC2Core20261025a MaassWeakOperatorCore20261024zz
open CompactC2ProductMollifier20261026a NestedCutoffDerivativeError20261026b

theorem nested_actual_energy_error_pointwise (Z Y : ℝ) (hZ : 0 < Z) (hY : 0 < Y)
    (hnest : ∀ z : UpperHalfPlane, globalCutoff Z z * globalCutoff Y z = globalCutoff Y z)
    (z : UpperHalfPlane) (c : ℂ) :
    cutoffEnergyH Y z * ‖(globalCutoff Z z : ℂ) * c‖^2 = cutoffEnergyH Y z * ‖c‖^2 := by
  have hχ := complexGlobalChart_cinfty Y hY
  have hψ := complexGlobalChart_cinfty Z hZ
  have hnestChart : ∀ p ∈ positiveChart,
      complexGlobalChart Z p * complexGlobalChart Y p = complexGlobalChart Y p := by
    intro p hp
    change (globalCutoff Z (chartLift p) : ℂ) * (globalCutoff Y (chartLift p) : ℂ) =
      (globalCutoff Y (chartLift p) : ℂ)
    exact_mod_cast hnest (chartLift p)
  have h := nested_derivative_error_localization positiveChart_isOpen hψ.continuousOn
    hnestChart z.im_pos (fun _ => c)
  have hx : directional ex (complexGlobalChart Y) (z.re,z.im) =
      sliceDx (complexGlobalChart Y) (z.re,z.im) :=
    (sliceDx_eq_fderiv _ (hχ.differentiableOn (by simp)) z.im_pos).symm
  have hy : directional ey (complexGlobalChart Y) (z.re,z.im) =
      sliceDy (complexGlobalChart Y) (z.re,z.im) :=
    (sliceDy_eq_fderiv _ (hχ.differentiableOn (by simp)) z.im_pos).symm
  have hval : complexGlobalChart Z (z.re,z.im) = (globalCutoff Z z : ℂ) := by
    simp only [complexGlobalChart, chartLift_pair]
  rw [hx,hy,hval] at h
  have hw := congrArg (fun r : ℝ => z.im^2 * r) h
  simpa only [cutoffEnergyH, hyperbolicChartDirichlet_self_re_eq, chartEnergySq,
    Complex.normSq_eq_norm_sq, mul_assoc] using hw

theorem quotient_nested_error_pointwise (N : ℕ) (Z Y : ℝ) (hZ : 0 < Z) (hY : 0 < Y)
    (hnest : ∀ z : UpperHalfPlane, globalCutoff Z z * globalCutoff Y z = globalCutoff Y z)
    (q : Gamma0OrbitSpace N) (c : ℂ) :
    quotientCutoffEnergy N Y hY q * ‖(quotientCutoff N Z q : ℂ) * c‖^2 =
      quotientCutoffEnergy N Y hY q * ‖c‖^2 :=
  Quotient.inductionOn q (fun z => nested_actual_energy_error_pointwise Z Y hZ hY hnest z c)

theorem actual_defect_quotient_error_integrable (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (Y : ℝ) (hY : 1 < Y) :
    Integrable (fun q => quotientCutoffEnergy N Y (lt_trans (by norm_num) hY) q * ‖f q‖^2)
      (carrierPushforward N) := actualCutoffError_quadratic_integrable N Y hY f

/-- The actual inner cutoff's full shifted energy is controlled by the
literal weighted gradient-cutoff error of the ORIGINAL quotient vector. -/
theorem actual_defect_cutoff_energy_eq_error (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (hf : f ∈ minimalShiftDefect N) (Y : ℝ) (hY : 1 < Y) :
    ‖actualDefectCutoffEnergyLift N f hf Y hY‖^2 =
      ∫ q, quotientCutoffEnergy N Y (lt_trans (by norm_num) hY) q * ‖f q‖^2
        ∂carrierPushforward N := by
  obtain ⟨Z,hZ,hnest,htest⟩ := actual_defect_nested_shifted_form_test N f hf Y hY
  let U := actualDefectCutoffEnergyLift N f hf Z hZ
  have hIMS := actualClosedFormCutoff_shifted_IMS N Y hY U
  dsimp only at hIMS
  rw [htest,Complex.zero_re,zero_add,actual_defect_nested_cutoff_lift N f hf Z Y hZ hY hnest]
    at hIMS
  have herr : (∫ q, quotientCutoffEnergy N Y (lt_trans (by norm_num) hY) q *
      ‖physicalProjection N U q‖^2 ∂carrierPushforward N) =
      ∫ q, quotientCutoffEnergy N Y (lt_trans (by norm_num) hY) q * ‖f q‖^2
        ∂carrierPushforward N := by
    dsimp only [U]
    rw [actualDefectCutoffEnergyLift_projection]
    apply integral_congr_ae
    filter_upwards [actual_cutoff_product_literal_ae N Z hZ f] with q hq
    rw [hq]
    exact quotient_nested_error_pointwise N Z Y (lt_trans (by norm_num) hZ)
      (lt_trans (by norm_num) hY) hnest q (f q)
  exact hIMS.trans herr

/-- Genuine global quotient mass/error inequality, now derived for
native adjoint defects with no regularity or testing premise. -/
theorem actual_defect_cutoff_norm_sq_le_error (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (hf : f ∈ minimalShiftDefect N) (Y : ℝ) (hY : 1 < Y) :
    ‖actualQuotientCutoffMultiplier N Y hY f‖^2 ≤
      ∫ q, quotientCutoffEnergy N Y (lt_trans (by norm_num) hY) q * ‖f q‖^2
        ∂carrierPushforward N := by
  have hn := physicalProjection_norm_le N (actualDefectCutoffEnergyLift N f hf Y hY)
  have hs := mul_self_le_mul_self (norm_nonneg _) hn
  simp only [← pow_two, actualDefectCutoffEnergyLift_projection] at hs
  exact hs.trans_eq (actual_defect_cutoff_energy_eq_error N f hf Y hY)

end
end ImbalancedChen.Part3.GammaActualDefectQuotientCaccioppoli20261026b
