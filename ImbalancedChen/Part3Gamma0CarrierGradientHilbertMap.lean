import ImbalancedChen.Part3Gamma0FriedrichsKernelZeroWeakGradient

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The two coordinate components need not descend individually to the scalar
orbit quotient. Instead they form a genuine vector L2 on the SAME canonical
carrier whose pushforward defines physical quotient volume. Its smooth-core
norm is exactly the geometric Dirichlet energy, so the actual energy closure
extends it with no overlap loss. The exact unshifted form identity is proved
by dense completion induction, rather than assumed as an energy hypothesis.
-/

namespace ImbalancedChen.Part3.Gamma0CarrierGradientHilbertMap20261026b
noncomputable section
open Set Filter MeasureTheory UniformSpace
open scoped UpperHalfPlane
open Gamma0FiniteMeasureCarrier20261024z
open Gamma0QuotientCellPushforward20261025a
open Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualEnergyCompletion20261025a
open Gamma0ActualFriedrichsOperator20261025a
open ActualGamma0CoreDirichletForm20261025a
open Gamma0PhysicalClosedDirichletForm20261025a
open Gamma0CompactCoreGradient20261025a
open Gamma0FriedrichsKernelZeroWeakGradient20261025a

def carrierVolume (N : ℕ) [NeZero N] : Measure UpperHalfPlane :=
  (volume : Measure UpperHalfPlane).restrict (gamma0Carrier N)

abbrev CarrierGradientL2 (N : ℕ) [NeZero N] :=
  Lp GradientFiber 2 (carrierVolume N)

theorem weightedCoreGradient_carrier_memLp (N : ℕ) [NeZero N]
    (u : EnergyCore N) : MemLp (weightedCoreGradient N u) 2 (carrierVolume N) := by
  apply (memLp_two_iff_integrable_sq_norm
    (weightedCoreGradient_continuous N u).aestronglyMeasurable).mpr
  have hd : Integrable (fun q => (coreDirichletDensity N u u q).re)
      ((carrierVolume N).map (orbitProjection N)) :=
    (coreDirichletDensity_integrable N u u).re
  have hp := hd.comp_measurable (orbitProjection_measurable N)
  simpa only [Function.comp_def, ← weightedCoreGradient_norm_sq] using hp

theorem weightedCoreGradient_carrier_integral (N : ℕ) [NeZero N]
    (u : EnergyCore N) :
    (∫ z, ‖weightedCoreGradient N u z‖ ^ 2 ∂carrierVolume N) =
      (coreDirichletForm N u u).re := by
  have hd := (coreDirichletDensity_integrable N u u).re
  calc
    _ = ∫ z, (coreDirichletDensity N u u (orbitProjection N z)).re
        ∂carrierVolume N := by
      apply integral_congr_ae
      exact Eventually.of_forall (weightedCoreGradient_norm_sq N u)
    _ = ∫ q, (coreDirichletDensity N u u q).re ∂carrierPushforward N :=
      (integral_map (orbitProjection_measurable N).aemeasurable
        hd.aestronglyMeasurable).symm
    _ = _ := integral_re (coreDirichletDensity_integrable N u u)

def carrierCoreGradient (N : ℕ) [NeZero N] (u : EnergyCore N) :
    CarrierGradientL2 N :=
  (weightedCoreGradient_carrier_memLp N u).toLp (weightedCoreGradient N u)

theorem carrierCoreGradient_coe_ae (N : ℕ) [NeZero N] (u : EnergyCore N) :
    carrierCoreGradient N u =ᵐ[carrierVolume N] weightedCoreGradient N u :=
  (weightedCoreGradient_carrier_memLp N u).coeFn_toLp

theorem carrierCoreGradient_norm_sq (N : ℕ) [NeZero N] (u : EnergyCore N) :
    ‖carrierCoreGradient N u‖ ^ 2 = (coreDirichletForm N u u).re := by
  have hn : (∫ z, ‖carrierCoreGradient N u z‖ ^ 2 ∂carrierVolume N) =
      ‖carrierCoreGradient N u‖ ^ 2 := by
    apply Complex.ofRealLI.injective
    simpa [← LinearIsometry.integral_comp_comm, inner_self_eq_norm_sq_to_K] using
      (L2.inner_def (𝕜 := ℂ) (carrierCoreGradient N u) (carrierCoreGradient N u)).symm
  rw [← hn, ← weightedCoreGradient_carrier_integral N u]
  apply integral_congr_ae
  filter_upwards [carrierCoreGradient_coe_ae N u] with z hz
  rw [hz]

def carrierCoreGradientLinear (N : ℕ) [NeZero N] :
    EnergyCore N →ₗ[ℂ] CarrierGradientL2 N where
  toFun := carrierCoreGradient N
  map_add' u v := by
    let hu := weightedCoreGradient_carrier_memLp N u
    let hv := weightedCoreGradient_carrier_memLp N v
    calc
      _ = (hu.add hv).toLp (weightedCoreGradient N u + weightedCoreGradient N v) :=
        MemLp.toLp_congr _ _ (Eventually.of_forall (fun z =>
          congrFun (weightedCoreGradient_add N u v) z))
      _ = _ := MemLp.toLp_add hu hv
  map_smul' c u := by
    let hu := weightedCoreGradient_carrier_memLp N u
    calc
      _ = (hu.const_smul c).toLp (c • weightedCoreGradient N u) :=
        MemLp.toLp_congr _ _ (Eventually.of_forall (fun z =>
          congrFun (weightedCoreGradient_smul N c u) z))
      _ = _ := MemLp.toLp_const_smul c hu

theorem carrierCoreGradient_bound (N : ℕ) [NeZero N] (u : EnergyCore N) :
    ‖carrierCoreGradientLinear N u‖ ≤ ‖coreEmbedding N u‖ := by
  rw [coreEmbedding_norm]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  change ‖carrierCoreGradient N u‖ ^ 2 ≤ ‖u‖ ^ 2
  rw [carrierCoreGradient_norm_sq]
  exact coreDirichlet_le_energy_norm_sq N u

/-- The native global gradient Hilbert map on physical carrier volume. -/
def completedCarrierGradient (N : ℕ) [NeZero N] :
    EnergyCompletion N →L[ℂ] CarrierGradientL2 N :=
  (carrierCoreGradientLinear N).extendOfNorm (coreEmbedding N).toLinearMap

theorem completedCarrierGradient_core (N : ℕ) [NeZero N] (u : EnergyCore N) :
    completedCarrierGradient N (coreEmbedding N u) = carrierCoreGradient N u := by
  exact LinearMap.extendOfNorm_eq (coreEmbedding_denseRange N)
    ⟨1, fun v => by simpa only [one_mul] using carrierCoreGradient_bound N v⟩ u

/-- The unshifted closed form is exactly the squared norm of the actual
vector gradient. There is no target energy-identity input. -/
theorem completedCarrierGradient_norm_sq (N : ℕ) [NeZero N]
    (e : EnergyCompletion N) :
    ‖completedCarrierGradient N e‖ ^ 2 = (actualDirichletPair N e e).re := by
  rw [actualDirichletPair_self_re_eq_energy_defect]
  refine Completion.induction_on e ?_ ?_
  · exact isClosed_eq ((completedCarrierGradient N).continuous.norm.pow 2)
      ((continuous_id.norm.pow 2).sub ((physicalProjection N).continuous.norm.pow 2))
  · intro u
    rw [completedCarrierGradient_core, carrierCoreGradient_norm_sq,
      coreEmbedding_norm, physicalProjection_core]
    have hd : ‖u‖ ^ 2 - ‖physicalCore N u‖ ^ 2 = (coreDirichletForm N u u).re := by
      rw [coreDirichletForm_eq_operatorPair]
      change ‖u‖ ^ 2 - ‖physicalCore N u‖ ^ 2 =
        (inner ℂ (physicalCore N u) (coreLaplacian N u)).re
      linarith [energy_norm_sq N u]
    exact hd.symm

/-- Every actual form-domain vector has this global represented gradient. -/
def actualFormCarrierGradient (N : ℕ) [NeZero N]
    (u : actualEnergyFormDomain N) : CarrierGradientL2 N :=
  completedCarrierGradient N (actualEnergyLift N u)

theorem actualFormCarrierGradient_energy (N : ℕ) [NeZero N]
    (u : actualEnergyFormDomain N) :
    ‖actualFormCarrierGradient N u‖ ^ 2 =
      (actualDirichletPair N (actualEnergyLift N u) (actualEnergyLift N u)).re :=
  completedCarrierGradient_norm_sq N (actualEnergyLift N u)

end
end ImbalancedChen.Part3.Gamma0CarrierGradientHilbertMap20261026b
