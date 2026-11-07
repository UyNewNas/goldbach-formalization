import ImbalancedChen.Part3GammaActualCutoffNativeCommutatorBudget

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual cutoff multiplication on the ORIGINAL smooth core has a native
minimal-operator-domain lift and a LINEAR actual operator output. The
output is the previously proved true native Leibniz quotient differential.
Subtracting the actual cutoff times the original core Laplacian therefore
constructs the genuine core commutator and proves its scalar quotient
representative, including BOTH first-gradient and Maass-cutoff terms.
-/

namespace ImbalancedChen.Part3.GammaActualCutoffCoreGraphOutput20261026b

noncomputable section
open Set Filter MeasureTheory
open scoped UpperHalfPlane
open MaassWeakOperatorCore20261024zz Gamma0CompactTensorPoincareC2Core20261025a
open Gamma0QuotientCellPushforward20261025a Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualSmoothQuotientMaassGraph20261025a Gamma0ActualMaassClosedOperator20261025a
open Gamma0ActualEnergyCompletion20261025a Gamma0CarrierMeasurableInverse20261025a
open Gamma0QuotientConullTransport20261025a ActualGamma0MaassDescent20261025a
open GammaSmoothMultiplierPeriodization20261026a GammaSmoothMultiplierLegalTests20261026a
open GammaNativeMaassLeibniz20261026a GammaActualQuotientCutoffMultiplier20261026b
open ActualModularCutoffMaassBudget20261025a GammaActualCutoffNativeCommutatorBudget20261026b

theorem actualCutoff_core_mem_minimalDomain
    (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y) (u : EnergyCore N) :
    actualQuotientCutoffMultiplier N Y hY (physicalCore N u) ∈ (actualClosedGammaMaass N).domain := by
  obtain ⟨U,V,hU,hV,hgraph⟩ := exists_legal_multiplied_core_test N u (complexGlobalH Y)
    (actualCutoff_isGammaInvariant N Y) (actualCutoff_cinfty Y (lt_trans (by norm_num) hY))
  have hUeq : U = actualQuotientCutoffMultiplier N Y hY (physicalCore N u) :=
    Lp.ext (hU.trans (actualQuotientCutoffMultiplier_coe_ae N Y hY (physicalCore N u)).symm)
  exact LinearPMap.mem_domain_iff.mpr ⟨V,by simpa only [hUeq] using hgraph⟩

def cutoffCoreDomainLinear (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y) :
    EnergyCore N →ₗ[ℂ] (actualClosedGammaMaass N).domain where
  toFun u := ⟨actualQuotientCutoffMultiplier N Y hY (physicalCore N u),
    actualCutoff_core_mem_minimalDomain N Y hY u⟩
  map_add' u v := Subtype.ext (by simp only [map_add])
  map_smul' c u := Subtype.ext (by simp only [map_smul])

def cutoffCoreOutputLinear (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y) :
    EnergyCore N →ₗ[ℂ] QuotientL2 N :=
  (actualClosedGammaMaass N).toFun.comp (cutoffCoreDomainLinear N Y hY)

theorem cutoffCoreOutput_graph (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y) (u : EnergyCore N) :
    (actualQuotientCutoffMultiplier N Y hY (physicalCore N u),cutoffCoreOutputLinear N Y hY u)
      ∈ (actualClosedGammaMaass N).graph :=
  LinearPMap.mem_graph _ (cutoffCoreDomainLinear N Y hY u)

theorem cutoffCoreOutput_native_ae
    (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y) (u : EnergyCore N) :
    (cutoffCoreOutputLinear N Y hY u : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
      quotientMultiplier N (multiplierDifferential (complexGlobalH Y) (coreRepresentative N u))
        (multiplierDifferential_invariant N _ _ (actualCutoff_isGammaInvariant N Y)
          (coreRepresentative_gamma0_invariant N u)
          ((actualCutoff_cinfty Y (lt_trans (by norm_num) hY)).of_le (by simp))
          ((coreRepresentative_cinfty N u).of_le (by simp))) := by
  obtain ⟨U,V,hU,hV,hgraph⟩ := exists_legal_multiplied_core_test N u (complexGlobalH Y)
    (actualCutoff_isGammaInvariant N Y) (actualCutoff_cinfty Y (lt_trans (by norm_num) hY))
  have hUeq : U = actualQuotientCutoffMultiplier N Y hY (physicalCore N u) :=
    Lp.ext (hU.trans (actualQuotientCutoffMultiplier_coe_ae N Y hY (physicalCore N u)).symm)
  have hVeq : V = cutoffCoreOutputLinear N Y hY u := by
    have h1 := hgraph
    have h2 := cutoffCoreOutput_graph N Y hY u
    rw [actualClosedGammaMaass_graph_eq,hUeq] at h1
    rw [actualClosedGammaMaass_graph_eq] at h2
    exact closedGammaGraph_right_unique N h1 h2
  simpa only [hVeq] using hV

theorem coreLaplacian_native_ae (N : ℕ) [NeZero N] (u : EnergyCore N) :
    (coreLaplacian N u : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
      quotientMultiplier N (upperMaass (coreRepresentative N u))
        (upperMaass_gamma0_invariant N _ ((coreRepresentative_cinfty N u).of_le (by simp))
          (coreRepresentative_gamma0_invariant N u)) := by
  rw [← reducedProjection_map_measure N,(reducedProjection_measurableEmbedding N).ae_map_iff]
  simpa only [outputPullback,quotientMultiplier_projection] using actualCoreLaplacian_actual N u

def coreCutoffCommutatorLinear (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y) :
    EnergyCore N →ₗ[ℂ] QuotientL2 N :=
  cutoffCoreOutputLinear N Y hY -
    (actualQuotientCutoffMultiplier N Y hY).toLinearMap.comp (coreLaplacian N)

def nativeCoreCutoffCommutator_invariant
    (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y) (u : EnergyCore N) :
    IsGammaInvariant N (nativeCutoffCommutator Y (coreRepresentative N u)) := by
  have hD := multiplierDifferential_invariant N (complexGlobalH Y) (coreRepresentative N u)
    (actualCutoff_isGammaInvariant N Y) (coreRepresentative_gamma0_invariant N u)
    ((actualCutoff_cinfty Y (lt_trans (by norm_num) hY)).of_le (by simp))
    ((coreRepresentative_cinfty N u).of_le (by simp))
  have hA := upperMaass_gamma0_invariant N (coreRepresentative N u)
    ((coreRepresentative_cinfty N u).of_le (by simp)) (coreRepresentative_gamma0_invariant N u)
  have hpoint (z : UpperHalfPlane) : nativeCutoffCommutator Y (coreRepresentative N u) z =
      multiplierDifferential (complexGlobalH Y) (coreRepresentative N u) z -
        complexGlobalH Y z * upperMaass (coreRepresentative N u) z := by
    unfold nativeCutoffCommutator multiplierDifferential
    ring
  intro gamma z
  rw [hpoint,hpoint,hD gamma z,complexGlobalH_invariant N Y gamma z,hA gamma z]

theorem coreCutoffCommutator_native_ae
    (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y) (u : EnergyCore N) :
    (coreCutoffCommutatorLinear N Y hY u : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
      quotientMultiplier N (nativeCutoffCommutator Y (coreRepresentative N u))
        (nativeCoreCutoffCommutator_invariant N Y hY u) := by
  have hquot : quotientMultiplier N (nativeCutoffCommutator Y (coreRepresentative N u))
      (nativeCoreCutoffCommutator_invariant N Y hY u) =
      quotientMultiplier N (multiplierDifferential (complexGlobalH Y) (coreRepresentative N u))
        (multiplierDifferential_invariant N _ _ (actualCutoff_isGammaInvariant N Y)
          (coreRepresentative_gamma0_invariant N u)
          ((actualCutoff_cinfty Y (lt_trans (by norm_num) hY)).of_le (by simp))
          ((coreRepresentative_cinfty N u).of_le (by simp))) -
      quotientMultiplier N (complexGlobalH Y) (actualCutoff_isGammaInvariant N Y) *
        quotientMultiplier N (upperMaass (coreRepresentative N u))
          (upperMaass_gamma0_invariant N _ ((coreRepresentative_cinfty N u).of_le (by simp))
            (coreRepresentative_gamma0_invariant N u)) := by
    funext q
    refine Quotient.inductionOn q (fun z => ?_)
    change nativeCutoffCommutator Y (coreRepresentative N u) z = _
    dsimp only [Pi.sub_apply,Pi.mul_apply,quotientMultiplier]
    unfold nativeCutoffCommutator multiplierDifferential
    ring
  change (cutoffCoreOutputLinear N Y hY u -
    actualQuotientCutoffMultiplier N Y hY (coreLaplacian N u) : QuotientL2 N) =ᵐ[carrierPushforward N] _
  filter_upwards [Lp.coeFn_sub (cutoffCoreOutputLinear N Y hY u)
      (actualQuotientCutoffMultiplier N Y hY (coreLaplacian N u)),
    cutoffCoreOutput_native_ae N Y hY u,
    actualQuotientCutoffMultiplier_coe_ae N Y hY (coreLaplacian N u),coreLaplacian_native_ae N u]
    with q hsub hout hcut hA
  simp only [Pi.mul_apply] at hcut
  rw [hsub,hout,hcut,hA]
  exact (congrFun hquot q).symm

end
end ImbalancedChen.Part3.GammaActualCutoffCoreGraphOutput20261026b
