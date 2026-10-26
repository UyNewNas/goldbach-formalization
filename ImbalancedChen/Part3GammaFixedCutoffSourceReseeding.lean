import ImbalancedChen.Part3GammaActualCutoffOperatorGraphConvergence
import ImbalancedChen.Part3ActualModularCutoffSmoothSeed

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

One genuine compact smooth seed sigma_Y traces the actual cutoff chi_Y.
Multiplication by an arbitrary original invariant core representative then
re-seeds chi_Y times that core vector in the SAME compact source support.
The actual Maass/periodization identity proves the actual native output.
No compact trace-one function or support-preserving density is assumed.
-/

namespace ImbalancedChen.Part3.GammaFixedCutoffSourceReseeding20261026b

noncomputable section
open Set Filter MeasureTheory
open scoped UpperHalfPlane
open MaassWeakOperatorCore20261024zz Gamma0CompactTensorPoincareC2Core20261025a
open Gamma0ComplexL1PoincareUnfolding20261025a Gamma0QuotientCellPushforward20261025a
open Gamma0CarrierMeasurableInverse20261025a Gamma0QuotientConullTransport20261025a
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualEnergyCompletion20261025a
open GammaSmoothMultiplierPeriodization20261026a GammaSmoothMultiplierLegalTests20261026a
open GammaNativeMaassLeibniz20261026a GammaActualQuotientCutoffMultiplier20261026b
open GammaActualCutoffCoreGraphOutput20261026b ActualCompactSeedMaassJoin20261025a
open ActualModularCutoffMaassBudget20261025a ActualModularCutoffSmoothSeed20261025a

structure FixedSmoothCutoffSeed (N : ℕ) (Y : ℝ) where
  seed : UpperHalfPlane → ℂ
  compact : HasCompactSupport seed
  smooth : ContDiffOn ℝ ∞ (extendUpper seed) positiveChart
  trace : complexSeedTrace N seed = complexGlobalH Y

theorem exists_fixedSmoothCutoffSeed (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y) :
    Nonempty (FixedSmoothCutoffSeed N Y) := by
  obtain ⟨sigma,hc,hs,ht⟩ := exists_compact_cinfty_seed_reconstructing_globalCutoff N Y hY.le
  exact ⟨⟨sigma,hc,hs,funext ht⟩⟩

def reseed {N : ℕ} [NeZero N] {Y : ℝ} (S : FixedSmoothCutoffSeed N Y)
    (u : EnergyCore N) : UpperHalfPlane → ℂ := coreRepresentative N u*S.seed

theorem reseed_support {N : ℕ} [NeZero N] {Y : ℝ} (S : FixedSmoothCutoffSeed N Y)
    (u : EnergyCore N) : Function.support (reseed S u) ⊆ tsupport S.seed :=
  multiplier_seed_support_subset (coreRepresentative N u) S.seed

theorem reseed_smooth {N : ℕ} [NeZero N] {Y : ℝ} (S : FixedSmoothCutoffSeed N Y)
    (u : EnergyCore N) : ContDiffOn ℝ ∞ (extendUpper (reseed S u)) positiveChart :=
  compact_multiplier_seed_smooth _ _ (coreRepresentative_cinfty N u) S.smooth

theorem reseed_trace {N : ℕ} [NeZero N] {Y : ℝ} (S : FixedSmoothCutoffSeed N Y)
    (u : EnergyCore N) : complexSeedTrace N (reseed S u) = complexGlobalH Y*coreRepresentative N u := by
  rw [reseed,complexSeedTrace_mul_invariant N _ _ (coreRepresentative_gamma0_invariant N u),S.trace]
  exact mul_comm _ _

theorem reseed_input_ae {N : ℕ} [NeZero N] {Y : ℝ} (S : FixedSmoothCutoffSeed N Y)
    (hY : 1 < Y) (u : EnergyCore N) :
    (actualQuotientCutoffMultiplier N Y hY (physicalCore N u) : Gamma0OrbitSpace N → ℂ)
      =ᵐ[carrierPushforward N] complexPoincare N (reseed S u) := by
  filter_upwards [actualQuotientCutoffMultiplier_coe_ae N Y hY (physicalCore N u),
    (chosenRepresentative_spec N u).1,reducedProjection_range_ae N] with q hq huq hsection
  obtain ⟨z,rfl⟩ := hsection
  rw [hq,huq,complexPoincare_projection]
  change complexGlobalH Y z*coreRepresentative N u z = complexSeedTrace N (reseed S u) z
  exact (congrFun (reseed_trace S u) z).symm

theorem reseed_output_ae {N : ℕ} [NeZero N] {Y : ℝ} (S : FixedSmoothCutoffSeed N Y)
    (hY : 1 < Y) (u : EnergyCore N) :
    (cutoffCoreOutputLinear N Y hY u : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
      complexPoincare N (upperMaass (reseed S u)) := by
  filter_upwards [cutoffCoreOutput_native_ae N Y hY u,reducedProjection_range_ae N]
    with q hq hsection
  obtain ⟨z,rfl⟩ := hsection
  rw [hq,complexPoincare_projection]
  change multiplierDifferential (complexGlobalH Y) (coreRepresentative N u) z =
    complexSeedTrace N (upperMaass (reseed S u)) z
  rw [← upperMaass_compactSeedTrace N (reseed S u) ((reseed_smooth S u).of_le (by simp))
    S.compact (reseed_support S u),reseed_trace S u]
  exact (upperMaass_mul (complexGlobalH Y) (coreRepresentative N u)
    ((actualCutoff_cinfty Y (lt_trans (by norm_num) hY)).of_le (by simp))
    ((coreRepresentative_cinfty N u).of_le (by simp)) z).symm

end
end ImbalancedChen.Part3.GammaFixedCutoffSourceReseeding20261026b
