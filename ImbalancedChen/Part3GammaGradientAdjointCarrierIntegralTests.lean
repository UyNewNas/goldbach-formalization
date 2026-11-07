import ImbalancedChen.Part3GammaClosedGradientAdjointCoreTests
import ImbalancedChen.Part3GammaFiniteSeedAdjointGraphTests

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Literal analytic carrier-vector tests for the native gradient adjoint.
The test vector is the actual weighted coordinate gradient of a finite
Poincare function on the canonical carrier; its separate components are
NOT asserted to descend as scalars. The right side is unfolded to the
original whole-H compact scalar seed. Both products are independently L1.
-/
namespace ImbalancedChen.Part3.GammaGradientAdjointCarrierIntegralTests20261026b
noncomputable section
open Set Filter MeasureTheory
open scoped Topology UpperHalfPlane
open MaassWeakOperatorCore20261024zz Gamma0CompactGreenProductL120261025a
open Gamma0CompactCoreGradient20261025a Gamma0CarrierGradientHilbertMap20261026b
open Gamma0SmoothCompactTensorCore20261025a Gamma0CompactTensorPoincareLocalFinite20261025a
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualSmoothQuotientMaassGraph20261025a
open Gamma0ActualEnergyCompletion20261025a Gamma0QuotientCellPushforward20261025a
open Gamma0ActualAdjointInteriorWeakEquation20261025a
open GammaActualClosedGradientRealization20261026b
open GammaClosedGradientAdjointCoreTests20261026b GammaFiniteSeedAdjointGraphTests20261026b

def finitePoincareGradient (N : ℕ) [NeZero N] (s : SmoothSeed) (z : UpperHalfPlane) : GradientFiber :=
  !₂[(z.im : ℂ) * sliceDx (extendUpper (smoothFinitePoincare N Finset.univ s.2)) (z.re,z.im),
    (z.im : ℂ) * sliceDy (extendUpper (smoothFinitePoincare N Finset.univ s.2)) (z.re,z.im)]

theorem finitePoincareGradient_eq (N : ℕ) [NeZero N] (s : SmoothSeed) :
    finitePoincareGradient N s = weightedCoreGradient N (seedCoreElement N s) := by
  funext z
  rw [weightedCoreGradient,coreRepresentative_seed]
  rfl

/-- Exact vector L2 pairing to the actual carrier integral. -/
theorem finite_gradient_inner_carrier_integral (N : ℕ) [NeZero N]
    (s : SmoothSeed) (g : CarrierGradientL2 N) :
    inner ℂ (carrierCoreGradient N (seedCoreElement N s : EnergyCore N)) g =
      ∫ z : UpperHalfPlane, inner ℂ (finitePoincareGradient N s z) (g z) ∂carrierVolume N := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [carrierCoreGradient_coe_ae N (seedCoreElement N s : EnergyCore N)] with z hz
  rw [hz,finitePoincareGradient_eq]

/-- Both literal products are L1 even before adjoint membership is known.
The global scalar quotient output is only pulled back on a compact seed. -/
theorem finite_gradient_adjoint_products_integrable (N : ℕ) [NeZero N]
    (s : SmoothSeed) (g : CarrierGradientL2 N) (w : QuotientL2 N) :
    Integrable (fun z : UpperHalfPlane => inner ℂ (finitePoincareGradient N s z) (g z)) (carrierVolume N) ∧
    Integrable (fun z : UpperHalfPlane => star (finiteCoreFunction Finset.univ (seedTensors s) z) *
      w (orbitProjection N z)) volume := by
  constructor
  · apply (L2.integrable_inner (𝕜 := ℂ)
      (carrierCoreGradient N (seedCoreElement N s : EnergyCore N)) g).congr
    filter_upwards [carrierCoreGradient_coe_ae N (seedCoreElement N s : EnergyCore N)] with z hz
    rw [hz,finitePoincareGradient_eq]
  · exact compact_seed_quotient_product_integrable N _
      (continuous_finiteCoreFunction Finset.univ (seedTensors s))
      (finiteCompactTensorSupportK_isCompact Finset.univ (seedTensors s))
      (finiteCoreFunction_support_subset Finset.univ (seedTensors s)) w

/-- Literal integral characterization; no global whole-H vector
periodization, covariance, or scalar component descent is inserted. -/
theorem actual_gradient_adjoint_graph_iff_carrier_integral_tests (N : ℕ) [NeZero N]
    (g : CarrierGradientL2 N) (w : QuotientL2 N) :
    (g,w) ∈ (actualClosedGradient N).adjoint.graph ↔
      ∀ s : SmoothSeed,
        (∫ z : UpperHalfPlane, inner ℂ (finitePoincareGradient N s z) (g z) ∂carrierVolume N) =
          ∫ z : UpperHalfPlane, star (finiteCoreFunction Finset.univ (seedTensors s) z) * w (orbitProjection N z) := by
  rw [actual_gradient_adjoint_graph_iff_finite_seed_tests]
  simp_rw [finite_gradient_inner_carrier_integral,finite_seed_input_unfold]

end
end ImbalancedChen.Part3.GammaGradientAdjointCarrierIntegralTests20261026b
