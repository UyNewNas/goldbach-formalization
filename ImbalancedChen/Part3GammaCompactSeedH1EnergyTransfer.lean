import ImbalancedChen.Part3GammaCompactSeedDirichletBudget
import ImbalancedChen.Part3GammaCompactSeedL2Transport
import ImbalancedChen.Part3GammaCompactSeedGraphTransport
import ImbalancedChen.Part3Gamma0ActualEnergyCompletion

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The actual shifted quotient-energy norm of an original finite SmoothSeed
is controlled by its literal compact seed H1 mass, with a uniform common
compact-overlap constant. The input L2 estimate is obtained from true
nonnegative unfolding, not from a pointwise supremum estimate. This is
the quantitative ingredient for transporting genuine H1 seed approximation
into the existing actual quotient energy completion.
-/

namespace ImbalancedChen.Part3.GammaCompactSeedH1EnergyTransfer20261026b
noncomputable section
open Set Function Filter MeasureTheory
open scoped UpperHalfPlane
open Gamma0QuotientCellPushforward20261025a Gamma0CompactGlobalOverlap20261025a
open Gamma0CompactTensorPoincareLocalFinite20261025a Gamma0CompactTensorPoincareC2Core20261025a
open Gamma0CompactTensorQuotientL2Core20261025a Gamma0CompactSeedQuotientL2Budget20261025a
open Gamma0CompactSeedSharpL2Budget20261025a GammaCompactSeedL2Transport20261026a
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualSmoothQuotientMaassGraph20261025a
open Gamma0ActualEnergyCompletion20261025a GammaCompactSeedDirichletBudget20261026b
open MaassWeakOperatorCore20261024zz

theorem scalar_L2_integral_sq {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (g : Lp ℂ 2 μ) : (∫ x, ‖g x‖^2 ∂μ) = ‖g‖^2 := by
  apply Complex.ofRealLI.injective
  simpa [← LinearIsometry.integral_comp_comm, inner_self_eq_norm_sq_to_K] using
    (L2.inner_def (𝕜 := ℂ) g g).symm

/-- Sharp input estimate on actual quotient L2, paid by the original
seed L2 integral and the actual compact effective-action overlap. -/
theorem seedL2_norm_sq_le (N : ℕ) [NeZero N]
    (a : UpperHalfPlane → ℂ) (ha : Continuous a)
    (K : Set UpperHalfPlane) (hK : IsCompact K) (hs : Function.support a ⊆ K) :
    ‖seedL2 N a ha K hK hs‖^2 ≤
      (compactOverlapBound N K : ℝ) * ∫ z : UpperHalfPlane, ‖a z‖^2 := by
  have hac : HasCompactSupport a := HasCompactSupport.of_support_subset_isCompact hK hs
  have hi := (ha.memLp_of_hasCompactSupport hac (p := (2 : ℝ≥0∞))).integrable_norm_pow
    (by decide : (2 : ℕ) ≠ 0)
  have hq := compactPoincare_memLp_two N a ha hK hs
  have hqi := hq.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hb := compactSeed_quotient_squareMass_budget N a ha.measurable hK hs
  have hnn : ∀ᵐ z ∂(volume : Measure UpperHalfPlane), 0 ≤ ‖a z‖^2 :=
    Eventually.of_forall fun _ => sq_nonneg _
  have hqnn : ∀ᵐ q ∂carrierPushforward N, 0 ≤ ‖complexPoincare N a q‖^2 :=
    Eventually.of_forall fun _ => sq_nonneg _
  change (∫⁻ q, ENNReal.ofReal (‖complexPoincare N a q‖^2) ∂carrierPushforward N) ≤
    ENNReal.ofReal (compactOverlapBound N K : ℝ) * ∫⁻ z, ENNReal.ofReal (‖a z‖^2) at hb
  rw [← ofReal_integral_eq_lintegral_ofReal hqi hqnn,
    ← ofReal_integral_eq_lintegral_ofReal hi hnn] at hb
  have hr := ENNReal.toReal_mono (by simp) hb
  have hmass : (∫ q, ‖complexPoincare N a q‖^2 ∂carrierPushforward N) =
      ‖seedL2 N a ha K hK hs‖^2 := by
    rw [← scalar_L2_integral_sq (carrierPushforward N) (seedL2 N a ha K hK hs)]
    apply integral_congr_ae
    filter_upwards [seedL2_ae N a ha K hK hs] with q hq
    rw [hq]
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Nat.cast_nonneg _),
    ENNReal.toReal_ofReal (integral_nonneg_of_ae hqnn),
    ENNReal.toReal_ofReal (integral_nonneg_of_ae hnn), hmass] using hr

/-- Input estimate in the original finite SmoothSeed ABI, with one
prescribed compact support container for an entire approximation family. -/
theorem finite_seed_input_norm_sq_le (N : ℕ) [NeZero N] (s : SmoothSeed)
    {K : Set UpperHalfPlane} (hK : IsCompact K)
    (hsK : finiteCompactTensorSupportK Finset.univ (seedTensors s) ⊆ K) :
    ‖seedVector N s‖^2 ≤ (compactOverlapBound N K : ℝ) *
      ∫ z : UpperHalfPlane, ‖finiteCoreFunction Finset.univ (seedTensors s) z‖^2 := by
  have hs := (finiteCoreFunction_support_subset Finset.univ (seedTensors s)).trans hsK
  have heq := GammaCompactSeedGraphTransport20261026a.compactInput_finiteTensor_eq N s.2 K hK hs
  rw [← heq]
  exact seedL2_norm_sq_le N _ (continuous_finiteCoreFunction Finset.univ (seedTensors s)) K hK hs

/-- This controls the genuine actual energy norm, including all cross
terms within each finite seed. No completed-domain membership is assumed. -/
theorem finite_seed_shifted_energy_norm_sq_le (N : ℕ) [NeZero N] (s : SmoothSeed)
    {K : Set UpperHalfPlane} (hK : IsCompact K)
    (hsK : finiteCompactTensorSupportK Finset.univ (seedTensors s) ⊆ K) :
    ‖(seedCoreElement N s : EnergyCore N)‖^2 ≤
      (compactOverlapBound N K : ℝ) *
        ((∫ z : UpperHalfPlane, ‖finiteCoreFunction Finset.univ (seedTensors s) z‖^2) +
          ∫ z : UpperHalfPlane, seedDirichletDensity Finset.univ (seedTensors s) z) := by
  have hm := finite_seed_input_norm_sq_le N s hK hsK
  have he := quotient_seed_Dirichlet_le N Finset.univ (seedTensors s) hK hsK
  rw [energy_norm_sq]
  change ‖seedVector N s‖^2 +
    (inner ℂ (seedVector N s) (actualCoreLaplacian N (seedCoreElement N s))).re ≤ _
  rw [actualCoreLaplacian_seed]
  change (inner ℂ (seedVector N s) (seedOutput N s)).re ≤ _ at he
  calc
    _ ≤ (compactOverlapBound N K : ℝ) *
        (∫ z : UpperHalfPlane, ‖finiteCoreFunction Finset.univ (seedTensors s) z‖^2) +
      (compactOverlapBound N K : ℝ) *
        (∫ z : UpperHalfPlane, seedDirichletDensity Finset.univ (seedTensors s) z) :=
      add_le_add hm he
    _ = _ := by ring

end
end ImbalancedChen.Part3.GammaCompactSeedH1EnergyTransfer20261026b
