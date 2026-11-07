import ImbalancedChen.Part3GammaActualCutoffNativeGradientBudget
import ImbalancedChen.Part3GammaCoreMultiplierGradientProduct

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The genuine smooth-product gradient supplier identifies the actual core
multiplier lift on the WHOLE physical carrier. Integrating the native
cutoff derivative budget gives one energy-norm bound independent of Y>1.
Mass is transported by the actual quotient pushforward; individual vector
gradient components are never falsely descended as scalar invariants.
-/

namespace ImbalancedChen.Part3.GammaActualCutoffCoreUniformEnergy20261026b

noncomputable section
open Set Filter MeasureTheory
open scoped UpperHalfPlane
open MaassWeakOperatorCore20261024zz Gamma0CompactTensorPoincareC2Core20261025a
open Gamma0QuotientCellPushforward20261025a Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualEnergyCompletion20261025a Gamma0ActualFriedrichsOperator20261025a
open Gamma0PhysicalClosedDirichletForm20261025a Gamma0CompactCoreGradient20261025a
open ActualGamma0CoreDirichletForm20261025a Gamma0CarrierGradientHilbertMap20261026b
open Gamma0CarrierGradientExhaustion20261026b GammaCoreMultiplierGradientProduct20261026b
open GammaSmoothMultiplierPeriodization20261026a GammaSmoothMultiplierLegalTests20261026a
open GammaSmoothCoreMultiplierEnergyLift20261026b GammaActualCutoffNativeGradientBudget20261026b
open ActualModularCutoffMaassBudget20261025a ActualCuspStripCutoff20261025a

theorem nativeWeightedGradient_norm_sq (F : UpperHalfPlane → ℂ) (z : UpperHalfPlane) :
    ‖nativeWeightedGradient F z‖^2 = nativeEnergySq F z := by
  rw [EuclideanSpace.norm_sq_eq,Fin.sum_univ_two]
  simp only [nativeWeightedGradient,PiLp.toLp_apply,Matrix.cons_val_zero,Matrix.cons_val_one,
    norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos z.im_pos,mul_pow,nativeEnergySq]
  ring

/-- Exact scalar native energy on the entire actual carrier; both
integrability and the closed-form identity are conclusions. -/
theorem coreMultiplierEnergyLift_native_energy
    (N : ℕ) [NeZero N] (u : smoothCore N) (chi : UpperHalfPlane → ℂ)
    (hc : IsGammaInvariant N chi)
    (hcs : ContDiffOn ℝ ∞ (extendUpper chi) positiveChart) :
    Integrable (fun z => nativeEnergySq (chi*coreRepresentative N u) z) (carrierVolume N) ∧
      (actualDirichletPair N (coreMultiplierEnergyLift N u chi hc hcs)
        (coreMultiplierEnergyLift N u chi hc hcs)).re =
        ∫ z, nativeEnergySq (chi*coreRepresentative N u) z ∂carrierVolume N := by
  let e := coreMultiplierEnergyLift N u chi hc hcs
  have hs : ContDiffOn ℝ 2 (extendUpper (chi*coreRepresentative N u)) positiveChart := by
    rw [extendUpper_mul]
    exact (hcs.of_le (by simp)).mul ((coreRepresentative_cinfty N u).of_le (by simp))
  have hg := completedCarrierGradient_eq_native N e (chi*coreRepresentative N u)
    (smoothCoreProduct_invariant N u chi hc) hs
    (coreMultiplierEnergyLift_smooth_representative_ae N u chi hc hcs)
  have hnorm : (fun z => ‖completedCarrierGradient N e z‖^2) =ᵐ[carrierVolume N]
      (fun z => nativeEnergySq (chi*coreRepresentative N u) z) := by
    filter_upwards [hg] with z hz
    rw [hz,nativeWeightedGradient_norm_sq]
  exact ⟨(completedCarrierGradient_integrable_norm_sq N e).congr hnorm,
    (actualDirichletPair_eq_carrier_gradient_integral N e).trans (integral_congr_ae hnorm)⟩

private theorem scalarLp_integral_norm_sq (N : ℕ) [NeZero N] (u : QuotientL2 N) :
    (∫ q, ‖u q‖^2 ∂carrierPushforward N) = ‖u‖^2 := by
  apply Complex.ofRealLI.injective
  simpa [← LinearIsometry.integral_comp_comm,inner_self_eq_norm_sq_to_K] using
    (L2.inner_def (𝕜 := ℂ) u u).symm

/-- True quotient mass, transported through its defining carrier map. -/
theorem coreRepresentative_carrier_mass (N : ℕ) [NeZero N] (u : smoothCore N) :
    Integrable (fun z => ‖coreRepresentative N u z‖^2) (carrierVolume N) ∧
      (∫ z, ‖coreRepresentative N u z‖^2 ∂carrierVolume N) = ‖(u : QuotientL2 N)‖^2 := by
  have hq := (Lp.memLp (u : QuotientL2 N)).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hc := hq.comp_measurable (orbitProjection_measurable N)
  have hraw : ∀ᵐ z ∂carrierVolume N,
      (u : QuotientL2 N) (orbitProjection N z) = coreRepresentative N u z :=
    ae_of_ae_map (orbitProjection_measurable N).aemeasurable (chosenRepresentative_spec N u).1
  have hnorm : (fun z => ‖(u : QuotientL2 N) (orbitProjection N z)‖^2)
      =ᵐ[carrierVolume N] (fun z => ‖coreRepresentative N u z‖^2) := by
    filter_upwards [hraw] with z hz
    rw [hz]
  refine ⟨hc.congr hnorm,?_⟩
  calc
    _ = ∫ z, ‖(u : QuotientL2 N) (orbitProjection N z)‖^2 ∂carrierVolume N :=
      integral_congr_ae hnorm.symm
    _ = ∫ q, ‖(u : QuotientL2 N) q‖^2 ∂carrierPushforward N :=
      (integral_map (orbitProjection_measurable N).aemeasurable hq.aestronglyMeasurable).symm
    _ = _ := scalarLp_integral_norm_sq N u

theorem native_core_energy_carrier_integral (N : ℕ) [NeZero N] (u : smoothCore N) :
    Integrable (fun z => nativeEnergySq (coreRepresentative N u) z) (carrierVolume N) ∧
      (∫ z, nativeEnergySq (coreRepresentative N u) z ∂carrierVolume N) =
        (coreDirichletForm N u u).re := by
  have heq : (fun z => ‖weightedCoreGradient N u z‖^2) =
      (fun z => nativeEnergySq (coreRepresentative N u) z) := by
    funext z
    exact nativeWeightedGradient_norm_sq (coreRepresentative N u) z
  have hi := (weightedCoreGradient_carrier_memLp N u).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  exact ⟨by simpa only [heq] using hi,
    by simpa only [heq] using weightedCoreGradient_carrier_integral N u⟩

theorem actualCutoffCoreEnergy_physical_contraction
    (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y) (u : EnergyCore N) :
    ‖physicalProjection N (actualCutoffCoreEnergy N Y (lt_trans (by norm_num) hY) u)‖ ≤
      ‖physicalCore N u‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [coreMultiplierEnergyLift_physical_ae N u (complexGlobalH Y)
    (actualCutoff_isGammaInvariant N Y) (actualCutoff_cinfty Y (lt_trans (by norm_num) hY))]
    with q hq
  have hchi : ‖quotientMultiplier N (complexGlobalH Y) (actualCutoff_isGammaInvariant N Y) q‖ ≤ 1 := by
    exact Quotient.inductionOn q (fun z => actualCutoff_norm_le_one Y hY.le z)
  rw [hq,Pi.mul_apply,norm_mul]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hchi (norm_nonneg ((u : QuotientL2 N) q))

/-- The genuine unshifted form energy obeys the actual derivative budget
with the TRUE mass term. No arbitrary L2 function is assumed bounded. -/
theorem actualCutoffCoreEnergy_Dirichlet_bound
    (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y) (u : EnergyCore N) :
    let e := actualCutoffCoreEnergy N Y (lt_trans (by norm_num) hY) u
    (actualDirichletPair N e e).re ≤
      2*(coreDirichletForm N u u).re + 2*cutoffEnergyConstant*‖physicalCore N u‖^2 := by
  have hp := coreMultiplierEnergyLift_native_energy N u (complexGlobalH Y)
    (actualCutoff_isGammaInvariant N Y) (actualCutoff_cinfty Y (lt_trans (by norm_num) hY))
  have hE := native_core_energy_carrier_integral N u
  have hM := coreRepresentative_carrier_mass N u
  have hupper := (hE.1.const_mul 2).add (hM.1.const_mul (2*cutoffEnergyConstant))
  have hbound := integral_mono_ae hp.1 hupper (Eventually.of_forall (fun z =>
    nativeEnergySq_actualCutoff_mul_le Y hY (coreRepresentative N u)
      ((coreRepresentative_cinfty N u).of_le (by simp)) z))
  rw [hp.2]
  calc
    _ ≤ ∫ z, 2*nativeEnergySq (coreRepresentative N u) z +
        (2*cutoffEnergyConstant)*‖coreRepresentative N u z‖^2 ∂carrierVolume N := hbound
    _ = _ := by
      rw [integral_add (hE.1.const_mul 2) (hM.1.const_mul (2*cutoffEnergyConstant)),
        integral_const_mul,integral_const_mul,hE.2,hM.2]
      rfl

/-- One proved bound, independent of Y>1, in the actual shifted form norm. -/
theorem actualCutoffCoreEnergy_uniform_bound
    (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y) (u : EnergyCore N) :
    ‖actualCutoffCoreEnergy N Y (lt_trans (by norm_num) hY) u‖ ≤
      Real.sqrt (2+2*cutoffEnergyConstant)*‖coreEmbedding N u‖ := by
  let e := actualCutoffCoreEnergy N Y (lt_trans (by norm_num) hY) u
  have hmass := actualCutoffCoreEnergy_physical_contraction N Y hY u
  have henergy := actualCutoffCoreEnergy_Dirichlet_bound N Y hY u
  have hshift : ‖e‖^2 = ‖physicalProjection N e‖^2 + (actualDirichletPair N e e).re := by
    unfold actualDirichletPair
    rw [Complex.sub_re,← InnerProductSpace.norm_sq_eq_re_inner,← InnerProductSpace.norm_sq_eq_re_inner]
    ring
  have hcore : ‖coreEmbedding N u‖^2 = ‖physicalCore N u‖^2+(coreDirichletForm N u u).re := by
    rw [coreEmbedding_norm,energy_norm_sq,coreDirichletForm_eq_operatorPair]
    rfl
  have hmassSq := pow_le_pow_left₀ (norm_nonneg _) hmass 2
  have hC := cutoffEnergyConstant_nonneg
  have hq := coreDirichletForm_self_re_nonneg N u
  have hsq : ‖e‖^2 ≤ (2+2*cutoffEnergyConstant)*‖coreEmbedding N u‖^2 := by
    nlinarith [mul_nonneg hC hq,sq_nonneg ‖physicalCore N u‖]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  simpa only [mul_pow,Real.sq_sqrt (by linarith : 0 ≤ 2+2*cutoffEnergyConstant)] using hsq

end
end ImbalancedChen.Part3.GammaActualCutoffCoreUniformEnergy20261026b
