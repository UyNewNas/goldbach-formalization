import ImbalancedChen.Part3GammaActualCutoffErrorQuadratic
import Mathlib.Tactic.Module

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Exact IMS for the actual closed-form cutoff on any form vector with a
genuine smooth invariant physical representative. It is proved from the
native product rule and full-carrier gradient identification. The square
test is the actual first-power cutoff operator applied TWICE. Every
mixed-density/error integral and the quotient pushforward are paid.
-/

namespace ImbalancedChen.Part3.GammaActualSmoothRepresentativeIMS20261026b

noncomputable section
open Set Filter MeasureTheory
open scoped UpperHalfPlane
open Gamma0QuotientCellPushforward20261025a Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualEnergyCompletion20261025a Gamma0ActualFriedrichsOperator20261025a
open Gamma0CarrierGradientHilbertMap20261026b Gamma0CarrierGradientExhaustion20261026b
open GammaSmoothMultiplierPeriodization20261026a GammaSmoothMultiplierLegalTests20261026a
open GammaNativeMaassLeibniz20261026a GammaCoreMultiplierGradientProduct20261026b
open GammaActualCutoffCoreUniformEnergy20261026b GammaActualCutoffNativeGradientBudget20261026b
open GammaActualQuotientCutoffMultiplier20261026b GammaActualClosedFormCutoffMultiplier20261026b
open GammaActualCutoffErrorQuadratic20261026b ActualModularCutoffMaassBudget20261025a
open ActualModularSmoothCuspCutoff20261025a ActualModularCutoffEnergyBudget20261025a

private theorem real_scalar_IMS {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (c : ℝ) (x d : H) :
    ‖(c : ℂ) • x + d‖^2 =
      (inner ℂ (((c^2 : ℝ) : ℂ) • x + ((2*c : ℝ) : ℂ) • d) x).re + ‖d‖^2 := by
  letI : InnerProductSpace ℝ H := InnerProductSpace.complexToReal
  have hr : ‖c • x+d‖^2 = inner ℝ (c^2 • x+(2*c) • d) x + ‖d‖^2 := by
    rw [norm_add_sq_real,inner_add_left,real_inner_smul_left,real_inner_smul_left,
      real_inner_self_eq_norm_sq,real_inner_smul_left,real_inner_comm d x]
    simp only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
    ring
  simpa only [RCLike.real_smul_eq_coe_smul (K := ℂ),real_inner_eq_re_inner] using hr

/-- Pointwise identity from TRUE native derivatives. Only the multiplier
VALUE is real; the test function and all gradients may be complex. -/
theorem native_real_multiplier_IMS (chi F : UpperHalfPlane → ℂ)
    (hcs : ContDiffOn ℝ 2 (extendUpper chi) positiveChart)
    (hFs : ContDiffOn ℝ 2 (extendUpper F) positiveChart)
    (z : UpperHalfPlane) (c : ℝ) (hc : chi z = (c : ℂ)) :
    ‖nativeWeightedGradient (chi*F) z‖^2 =
      (inner ℂ (nativeWeightedGradient (chi*(chi*F)) z) (nativeWeightedGradient F z)).re +
        nativeEnergySq chi z * ‖F z‖^2 := by
  have hprod : ContDiffOn ℝ 2 (extendUpper (chi*F)) positiveChart := by
    rw [extendUpper_mul]
    exact hcs.mul hFs
  have hg1 := nativeWeightedGradient_mul chi F hcs hFs z
  have hg2 := nativeWeightedGradient_mul chi (chi*F) hcs hprod z
  have hsq : nativeWeightedGradient (chi*(chi*F)) z =
      ((c^2 : ℝ) : ℂ) • nativeWeightedGradient F z +
        ((2*c : ℝ) : ℂ) • (F z • nativeWeightedGradient chi z) := by
    rw [hg2,hg1,hc]
    simp only [Pi.mul_apply,Complex.ofReal_pow,Complex.ofReal_mul,Complex.ofReal_ofNat]
    module
  rw [hg1,hc,hsq,real_scalar_IMS]
  rw [norm_smul,mul_pow,nativeWeightedGradient_norm_sq]
  ring

def cutoffProductInvariant (N : ℕ) (Y : ℝ) (F : UpperHalfPlane → ℂ)
    (hFi : IsGammaInvariant N F) : IsGammaInvariant N (complexGlobalH Y*F) := by
  intro gamma z
  simp only [Pi.mul_apply,complexGlobalH_invariant N Y gamma z,hFi gamma z]

theorem actualCutoff_smooth_representative_ae
    (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y) (e : EnergyCompletion N)
    (F : UpperHalfPlane → ℂ) (hFi : IsGammaInvariant N F)
    (hrep : ((physicalProjection N e : QuotientL2 N) : Gamma0OrbitSpace N → ℂ)
      =ᵐ[carrierPushforward N] quotientMultiplier N F hFi) :
    ((physicalProjection N (actualClosedFormCutoff N Y hY e) : QuotientL2 N) :
      Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
      quotientMultiplier N (complexGlobalH Y*F) (cutoffProductInvariant N Y F hFi) := by
  have hcoeff : quotientMultiplier N (complexGlobalH Y*F) (cutoffProductInvariant N Y F hFi) =
      quotientMultiplier N (complexGlobalH Y) (actualCutoff_isGammaInvariant N Y) *
        quotientMultiplier N F hFi := by
    funext q
    exact Quotient.inductionOn q (fun z => rfl)
  rw [actualClosedFormCutoff_physical,hcoeff]
  filter_upwards [actualQuotientCutoffMultiplier_coe_ae N Y hY (physicalProjection N e),hrep]
    with q hq hFq
  simpa only [Pi.mul_apply,hFq] using hq

/-- Exact actual closed-form IMS on the smooth-representative seam.
The physical quotient square is operator composition, never an assumed
independent cutoff action or a caller-supplied IMS identity. -/
theorem actualClosedFormCutoff_IMS_of_smooth_representative
    (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y) (e : EnergyCompletion N)
    (F : UpperHalfPlane → ℂ) (hFi : IsGammaInvariant N F)
    (hFs : ContDiffOn ℝ 2 (extendUpper F) positiveChart)
    (hrep : ((physicalProjection N e : QuotientL2 N) : Gamma0OrbitSpace N → ℂ)
      =ᵐ[carrierPushforward N] quotientMultiplier N F hFi) :
    let M := actualClosedFormCutoff N Y hY
    (actualDirichletPair N (M e) (M e)).re = (actualDirichletPair N (M (M e)) e).re +
      ∫ q, quotientCutoffEnergy N Y (lt_trans (by norm_num) hY) q *
        ‖physicalProjection N e q‖^2 ∂carrierPushforward N := by
  let M := actualClosedFormCutoff N Y hY
  let chi := complexGlobalH Y
  have hcs : ContDiffOn ℝ 2 (extendUpper chi) positiveChart :=
    (actualCutoff_cinfty Y (lt_trans (by norm_num) hY)).of_le (by simp)
  have hprod : ContDiffOn ℝ 2 (extendUpper (chi*F)) positiveChart := by
    rw [extendUpper_mul]
    exact hcs.mul hFs
  have hrep1 := actualCutoff_smooth_representative_ae N Y hY e F hFi hrep
  have hrep2 := actualCutoff_smooth_representative_ae N Y hY (M e) (chi*F)
    (cutoffProductInvariant N Y F hFi) hrep1
  have hG0 := completedCarrierGradient_eq_native N e F hFi hFs hrep
  have hG1 := completedCarrierGradient_eq_native N (M e) (chi*F)
    (cutoffProductInvariant N Y F hFi) hprod hrep1
  have hprod2 : ContDiffOn ℝ 2 (extendUpper (chi*(chi*F))) positiveChart := by
    rw [extendUpper_mul]
    exact hcs.mul hprod
  have hG2 := completedCarrierGradient_eq_native N (M (M e)) (chi*(chi*F))
    (cutoffProductInvariant N Y (chi*F) (cutoffProductInvariant N Y F hFi)) hprod2 hrep2
  have hraw : ∀ᵐ z ∂carrierVolume N, physicalProjection N e (orbitProjection N z) = F z := by
    have hh := ae_of_ae_map (orbitProjection_measurable N).aemeasurable hrep
    simpa only [quotientMultiplier_projection] using hh
  have hpoint : ∀ᵐ z ∂carrierVolume N,
      ‖completedCarrierGradient N (M e) z‖^2 =
        (inner ℂ (completedCarrierGradient N (M (M e)) z) (completedCarrierGradient N e z)).re +
        quotientCutoffEnergy N Y (lt_trans (by norm_num) hY) (orbitProjection N z) *
          ‖physicalProjection N e (orbitProjection N z)‖^2 := by
    filter_upwards [hG0,hG1,hG2,hraw] with z hz0 hz1 hz2 hzf
    rw [hz0,hz1,hz2,hzf,quotientCutoffEnergy_projection,← nativeEnergySq_actualCutoff]
    exact native_real_multiplier_IMS chi F hcs hFs z (globalCutoff Y z) rfl
  have herr := actualCutoffError_quadratic_integrable N Y hY (physicalProjection N e)
  have herrCarrier := herr.comp_measurable (orbitProjection_measurable N)
  have hmixed := L2.integrable_inner (𝕜 := ℂ)
    (completedCarrierGradient N (M (M e))) (completedCarrierGradient N e)
  change (actualDirichletPair N (M e) (M e)).re = _
  rw [actualDirichletPair_eq_carrier_gradient_integral,
    ← completedCarrierGradient_re_inner N (M (M e)) e,L2.inner_def,← integral_re hmixed,
    integral_map (orbitProjection_measurable N).aemeasurable herr.aestronglyMeasurable,
    ← integral_add hmixed.re herrCarrier]
  exact integral_congr_ae hpoint

end
end ImbalancedChen.Part3.GammaActualSmoothRepresentativeIMS20261026b
