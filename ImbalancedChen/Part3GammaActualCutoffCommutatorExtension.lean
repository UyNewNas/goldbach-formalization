import ImbalancedChen.Part3GammaActualCutoffCoreGraphOutput

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual native core commutator extends to a bounded map from the
EXISTING energy completion to the SAME physical quotient L2. Its uniform
bound comes from the genuine native density estimate, actual quotient
mass and actual geometric core Dirichlet energy. Original-core eventual
fixedness forces the commutator to be eventually exactly zero; density
then proves strong commutator decay for every existing energy vector.
No graph-output convergence or arbitrary cutoff-domain premise is used.
-/

namespace ImbalancedChen.Part3.GammaActualCutoffCommutatorExtension20261026b

noncomputable section
open Set Filter MeasureTheory
open scoped Topology UpperHalfPlane
open MaassWeakOperatorCore20261024zz Gamma0CompactTensorPoincareC2Core20261025a
open Gamma0QuotientCellPushforward20261025a Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualEnergyCompletion20261025a Gamma0ActualFriedrichsOperator20261025a
open ActualGamma0CoreDirichletForm20261025a Gamma0CompactCoreGradient20261025a
open GammaCoreMultiplierGradientProduct20261026b GammaActualCutoffCoreUniformEnergy20261026b
open GammaSmoothMultiplierPeriodization20261026a GammaSmoothMultiplierLegalTests20261026a
open GammaSmoothCoreMultiplierEnergyLift20261026b GammaOriginalCutoffCoreEnergyExact20261026b
open GammaActualCutoffCoreGraphOutput20261026b GammaActualCutoffNativeCommutatorBudget20261026b
open GammaActualCutoffNativeGradientBudget20261026b GammaCompactSeedCutoffPlateau20261026a
open ActualModularCutoffMaassBudget20261025a ActualCuspStripCutoff20261025a
open ActualCuspStripCutoffGraph20261025a ActualCompactSeedMaassJoin20261025a
open Gamma0WeightedCutoffDefectLimit20261026a

private theorem scalarLp_integral_norm_sq (N : ℕ) [NeZero N] (f : QuotientL2 N) :
    (∫ q, ‖f q‖^2 ∂carrierPushforward N) = ‖f‖^2 := by
  apply Complex.ofRealLI.injective
  simpa [← LinearIsometry.integral_comp_comm,inner_self_eq_norm_sq_to_K] using
    (L2.inner_def (𝕜 := ℂ) f f).symm

theorem coreCutoffCommutator_norm_square_bound
    (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y) (u : EnergyCore N) :
    ‖coreCutoffCommutatorLinear N Y hY u‖^2 ≤
      2*cutoffGraphConstant*‖physicalCore N u‖^2 +
        8*cutoffEnergyConstant*(coreDirichletForm N u u).re := by
  let F := coreRepresentative N u
  let qF := quotientMultiplier N F (coreRepresentative_gamma0_invariant N u)
  have hF : (physicalCore N u : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N] qF := by
    have hq : qF = chosenQuotientRepresentative N u := by
      funext q
      exact Quotient.inductionOn q (fun z => rfl)
    rw [hq]
    exact (chosenRepresentative_spec N u).1
  have hbound (q : Gamma0OrbitSpace N) :
      ‖quotientMultiplier N (nativeCutoffCommutator Y F)
        (nativeCoreCutoffCommutator_invariant N Y hY u) q‖^2 ≤
      2*cutoffGraphConstant*‖qF q‖^2 + 8*cutoffEnergyConstant*(coreDirichletDensity N u u q).re := by
    refine Quotient.inductionOn q (fun z => ?_)
    have hE : nativeEnergySq F z = (coreDirichletDensity N u u (orbitProjection N z)).re :=
      (nativeWeightedGradient_norm_sq F z).symm.trans (weightedCoreGradient_norm_sq N u z)
    change ‖nativeCutoffCommutator Y F z‖^2 ≤
      2*cutoffGraphConstant*‖F z‖^2 + 8*cutoffEnergyConstant*(coreDirichletDensity N u u (orbitProjection N z)).re
    rw [← hE]
    exact nativeCutoffCommutator_square_bound Y hY F z
  have hc := (Lp.memLp (coreCutoffCommutatorLinear N Y hY u)).integrable_norm_pow
    (by decide : (2 : ℕ) ≠ 0)
  have hu := (Lp.memLp (physicalCore N u)).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hd := (coreDirichletDensity_integrable N u u).re
  have hb := integral_mono_ae hc ((hu.const_mul (2*cutoffGraphConstant)).add
      (hd.const_mul (8*cutoffEnergyConstant))) (by
    filter_upwards [coreCutoffCommutator_native_ae N Y hY u,hF] with q hcq huq
    rw [hcq,huq]
    exact hbound q)
  have hD : (∫ q, (coreDirichletDensity N u u q).re ∂carrierPushforward N) =
      (coreDirichletForm N u u).re := integral_re (coreDirichletDensity_integrable N u u)
  rw [integral_add (hu.const_mul (2*cutoffGraphConstant)) (hd.const_mul (8*cutoffEnergyConstant)),
    integral_const_mul,integral_const_mul,scalarLp_integral_norm_sq,
    scalarLp_integral_norm_sq,hD] at hb
  exact hb

def cutoffCommutatorBound : ℝ := Real.sqrt (2*cutoffGraphConstant+8*cutoffEnergyConstant)

theorem cutoffCommutatorBound_nonneg : 0 ≤ cutoffCommutatorBound := Real.sqrt_nonneg _

theorem coreCutoffCommutator_uniform_bound
    (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y) (u : EnergyCore N) :
    ‖coreCutoffCommutatorLinear N Y hY u‖ ≤ cutoffCommutatorBound*‖coreEmbedding N u‖ := by
  have hb := coreCutoffCommutator_norm_square_bound N Y hY u
  have hcore : ‖coreEmbedding N u‖^2 = ‖physicalCore N u‖^2+(coreDirichletForm N u u).re := by
    rw [coreEmbedding_norm,energy_norm_sq,coreDirichletForm_eq_operatorPair]
    rfl
  have hC := cutoffEnergyConstant_nonneg
  have hK := cutoffGraphConstant_nonneg
  have hq := coreDirichletForm_self_re_nonneg N u
  have hsq : ‖coreCutoffCommutatorLinear N Y hY u‖^2 ≤
      (2*cutoffGraphConstant+8*cutoffEnergyConstant)*‖coreEmbedding N u‖^2 := by
    nlinarith [mul_nonneg hC (sq_nonneg ‖physicalCore N u‖),mul_nonneg hK hq]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg cutoffCommutatorBound_nonneg (norm_nonneg _))).mp
  simpa only [cutoffCommutatorBound,mul_pow,Real.sq_sqrt
    (show 0 ≤ 2*cutoffGraphConstant+8*cutoffEnergyConstant by positivity)] using hsq

def actualCutoffCommutator (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y) :
    EnergyCompletion N →L[ℂ] QuotientL2 N :=
  (coreCutoffCommutatorLinear N Y hY).extendOfNorm (coreEmbedding N).toLinearMap

theorem actualCutoffCommutator_core (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y) (u : EnergyCore N) :
    actualCutoffCommutator N Y hY (coreEmbedding N u) = coreCutoffCommutatorLinear N Y hY u :=
  LinearMap.extendOfNorm_eq (coreEmbedding_denseRange N)
    ⟨cutoffCommutatorBound,coreCutoffCommutator_uniform_bound N Y hY⟩ u

theorem actualCutoffCommutator_norm_le (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y)
    (e : EnergyCompletion N) : ‖actualCutoffCommutator N Y hY e‖ ≤ cutoffCommutatorBound*‖e‖ :=
  LinearMap.norm_extendOfNorm_apply_le (f := coreCutoffCommutatorLinear N Y hY)
    (e := (coreEmbedding N).toLinearMap) (coreEmbedding_denseRange N) cutoffCommutatorBound
    (coreCutoffCommutator_uniform_bound N Y hY) e

/-- The eventual vanishing is a genuine functional-neighborhood argument,
not a derivative assertion extracted from one cutoff value. -/
theorem exists_coreCutoffCommutator_eventual_zero
    (N : ℕ) [NeZero N] (u : EnergyCore N) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧ ∀ Y : ℝ, plateauThreshold a b ≤ Y → ∀ hY : 1 < Y,
      coreCutoffCommutatorLinear N Y hY u = 0 := by
  obtain ⟨a,b,ha,hab,hexact⟩ := exists_actualCutoffCoreEnergy_eventual_exact N u
  refine ⟨a,b,ha,hab,?_⟩
  intro Y hplateau hY
  have hrep := coreMultiplierEnergyLift_smooth_representative_ae N u (complexGlobalH Y)
    (actualCutoff_isGammaInvariant N Y) (actualCutoff_cinfty Y (lt_trans (by norm_num) hY))
  change ((physicalProjection N (actualCutoffCoreEnergy N Y (lt_trans (by norm_num) hY) u) :
      QuotientL2 N) : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N] _ at hrep
  rw [hexact Y hplateau,physicalProjection_core] at hrep
  have hprod : ContDiffOn ℝ 2 (extendUpper (complexGlobalH Y*coreRepresentative N u)) positiveChart := by
    rw [extendUpper_mul]
    exact ((actualCutoff_cinfty Y (lt_trans (by norm_num) hY)).of_le (by simp)).mul
      ((coreRepresentative_cinfty N u).of_le (by simp))
  have hcont : Continuous (quotientMultiplier N (complexGlobalH Y*coreRepresentative N u)
      (smoothCoreProduct_invariant N u (complexGlobalH Y) (actualCutoff_isGammaInvariant N Y)) ∘
        orbitProjection N) := native_C2_continuous _ hprod
  have hfix : complexGlobalH Y*coreRepresentative N u = coreRepresentative N u :=
    (coreRepresentative_eq N u _ hrep hcont).symm
  have hzero := nativeCutoffCommutator_eq_zero_of_fixed Y (lt_trans (by norm_num) hY)
    (coreRepresentative N u) ((coreRepresentative_cinfty N u).of_le (by simp)) hfix
  apply Lp.ext
  filter_upwards [coreCutoffCommutator_native_ae N Y hY u,
    Lp.coeFn_zero ℂ 2 (carrierPushforward N)] with q hq hz
  rw [hq,hz]
  exact Quotient.inductionOn q (fun z => by simpa only [Pi.zero_apply] using congrFun hzero z)

/-- PROVED strong commutator decay on every existing energy vector. -/
theorem actualCutoffCommutator_tendsto_zero (N : ℕ) [NeZero N] (e : EnergyCompletion N) :
    Tendsto (fun n => actualCutoffCommutator N (cutoffHeight n) (cutoffHeight_gt_one n) e)
      atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro epsilon hepsilon
  let B := cutoffCommutatorBound
  have hB : 0 ≤ B := cutoffCommutatorBound_nonneg
  have hBp : 0 < B+1 := by linarith
  obtain ⟨w,hw,hnear⟩ := Metric.mem_closure_iff.mp ((coreEmbedding_denseRange N) e)
    (epsilon/(B+1)) (div_pos hepsilon hBp)
  obtain ⟨u,rfl⟩ := hw
  have hnorm : ‖e-coreEmbedding N u‖ < epsilon/(B+1) := by simpa only [dist_eq_norm] using hnear
  have hsmall : (B+1)*‖e-coreEmbedding N u‖ < epsilon := by
    simpa only [mul_comm] using (lt_div_iff₀ hBp).mp hnorm
  obtain ⟨a,b,ha,hab,hzero⟩ := exists_coreCutoffCommutator_eventual_zero N u
  filter_upwards [cutoffHeight_tendsto.eventually (eventually_ge_atTop (plateauThreshold a b))]
    with n hn
  have hz : actualCutoffCommutator N (cutoffHeight n) (cutoffHeight_gt_one n) (coreEmbedding N u) = 0 := by
    rw [actualCutoffCommutator_core]
    exact hzero (cutoffHeight n) hn (cutoffHeight_gt_one n)
  rw [dist_zero_right]
  calc
    _ = ‖actualCutoffCommutator N (cutoffHeight n) (cutoffHeight_gt_one n) (e-coreEmbedding N u)‖ := by
      rw [map_sub,hz,sub_zero]
    _ ≤ B*‖e-coreEmbedding N u‖ := actualCutoffCommutator_norm_le N _ _ _
    _ ≤ (B+1)*‖e-coreEmbedding N u‖ := by nlinarith [norm_nonneg (e-coreEmbedding N u)]
    _ < epsilon := hsmall

end
end ImbalancedChen.Part3.GammaActualCutoffCommutatorExtension20261026b
