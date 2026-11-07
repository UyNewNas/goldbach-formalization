import ImbalancedChen.Part3Gamma0ComplexL1PoincareUnfolding
import ImbalancedChen.Part3Gamma0CompactTensorQuotientL2Core
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-!
# Actual Gamma0 quotient pairing unfolded against one compact seed

SOURCE_WRITTEN / UNCOMPILED / NOT_ROOT_ACCEPTED / CODE_ONLY.

Both quotient functions are the genuine full effective-Gamma0 Poincare
objects. Only the first SEED is compact on H. Its product with the full
continuous second Poincare function is genuinely L1, so the proved
complex L1 unfolding applies. Actual Gamma0 invariance moves the full
second factor outside the seed trace. The actual quotient measure map
then gives the same identity for the actual quotient L2 inner product.

No quotient Green identity or differential commutation is assumed or
asserted. This is the needed one-compact unfolding prerequisite.
-/

namespace ImbalancedChen.Part3.Gamma0PoincarePairingUnfolding20261025a

noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane Pointwise
open ImbalancedChen.Part3.Gamma0EffectiveActionKernel20261024z
open ImbalancedChen.Part3.Gamma0EffectiveFiniteUnfolding20261025a
open ImbalancedChen.Part3.Gamma0CarrierAESection20261025a
open ImbalancedChen.Part3.Gamma0CarrierMeasurableInverse20261025a
open ImbalancedChen.Part3.Gamma0QuotientConullTransport20261025a
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz
open ImbalancedChen.Part3.MaassFiniteCoreL2Graph20261025a
open ImbalancedChen.Part3.Gamma0CompactTensorPoincareLocalFinite20261025a
open ImbalancedChen.Part3.Gamma0CompactTensorPoincareC2Core20261025a
open ImbalancedChen.Part3.Gamma0CompactTensorQuotientL2Core20261025a
open ImbalancedChen.Part3.Gamma0ComplexL1PoincareUnfolding20261025a

/-- One compact SEED paired with a full, generally noncompact Poincare
function on H. No truncation of the second Poincare series is used. -/
def pairingSeed (N : ℕ) {ι κ : Type*} (s : Finset ι) (T : ι → CompactTensor)
    (t : Finset κ) (U : κ → CompactTensor) (z : UpperHalfPlane) : ℂ :=
  star (finiteCoreFunction s T z) * finiteCompactTensorPoincare N t U z

theorem finiteCoreFunction_hasCompactSupport {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) : HasCompactSupport (finiteCoreFunction s T) :=
  HasCompactSupport.of_support_subset_isCompact (finiteCompactTensorSupportK_isCompact s T)
    (finiteCoreFunction_support_subset s T)

/-- Seed integrability is proved by actual compact support and continuity
against canonical hyperbolic volume, rather than supplied as a norm bound. -/
theorem pairingSeed_integrable (N : ℕ) {ι κ : Type*}
    (s : Finset ι) (T : ι → CompactTensor) (t : Finset κ) (U : κ → CompactTensor) :
    Integrable (pairingSeed N s T t U) (volume : Measure UpperHalfPlane) := by
  have hc : HasCompactSupport (fun z => star (finiteCoreFunction s T z)) :=
    (finiteCoreFunction_hasCompactSupport s T).comp_left (g := star) (by simp)
  exact ((continuous_finiteCoreFunction s T).star.mul
    (finiteCompactTensorPoincare_continuous N t U)).integrable_of_hasCompactSupport hc.mul_right

/-- The FULL second Poincare factor is invariant under every actual
effective matrix action, so it factors out of the compact seed trace. -/
theorem pairingSeed_trace (N : ℕ) {ι κ : Type*}
    (s : Finset ι) (T : ι → CompactTensor) (t : Finset κ) (U : κ → CompactTensor)
    (z : UpperHalfPlane) :
    complexSeedTrace N (pairingSeed N s T t U) z =
      star (finiteCompactTensorPoincare N s T z) * finiteCompactTensorPoincare N t U z := by
  unfold complexSeedTrace translatedSeed pairingSeed
  calc
    _ = ∑' q : effectiveGamma0 N,
        star (finiteCoreFunction s T (effectiveMatrixAction N q z)) *
          finiteCompactTensorPoincare N t U z := by
      apply tsum_congr
      intro q
      rw [show finiteCompactTensorPoincare N t U (effectiveMatrixAction N q z) =
        finiteCompactTensorPoincare N t U z from
          finiteCompactTensorPoincare_gamma0_invariant N t U (effectiveRepresentative N q) z]
    _ = _ := by
      rw [tsum_mul_right, ← tsum_star]
      rfl

/-- Actual quotient integrability follows from the independently proved
L2 membership of both genuine quotient Poincare functions. -/
theorem quotient_pairing_integrable (N : ℕ) [NeZero N] {ι κ : Type*}
    (s : Finset ι) (T : ι → CompactTensor) (t : Finset κ) (U : κ → CompactTensor) :
    Integrable (fun q => star (quotientTensorPoincare N s T q) * quotientTensorPoincare N t U q)
      (carrierPushforward N) := by
  exact MemLp.integrable_mul (p := 2) (q := 2)
    (quotientTensorPoincare_memLp_two N s T).star (quotientTensorPoincare_memLp_two N t U)

/-- Genuine one-compact actual quotient unfolding. This is the original
spatial quotient measure, indexed once per full central action kernel. -/
theorem quotient_poincare_pairing_unfolding (N : ℕ) [NeZero N] {ι κ : Type*}
    (s : Finset ι) (T : ι → CompactTensor) (t : Finset κ) (U : κ → CompactTensor) :
    (∫ q, star (quotientTensorPoincare N s T q) * quotientTensorPoincare N t U q
      ∂carrierPushforward N) =
      ∫ z : UpperHalfPlane, star (finiteCoreFunction s T z) * finiteCompactTensorPoincare N t U z := by
  calc
    _ = ∫ z : reducedCarrier N,
        star (finiteCompactTensorPoincare N s T z) * finiteCompactTensorPoincare N t U z
          ∂reducedCarrierMeasure N := by
      rw [← reducedProjection_map_measure N,
        (reducedProjection_measurableEmbedding N).integral_map]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun z => rfl)
    _ = ∫ z in reducedCarrier N,
        star (finiteCompactTensorPoincare N s T z) * finiteCompactTensorPoincare N t U z :=
      integral_subtype_comap (reducedCarrier_measurable N) _
    _ = ∫ z in reducedCarrier N, complexSeedTrace N (pairingSeed N s T t U) z := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun z => (pairingSeed_trace N s T t U z).symm)
    _ = _ := complex_carrier_unfolding N (pairingSeed N s T t U) (pairingSeed_integrable N s T t U)

/-- The actual quotient Hilbert pairing acquires the same compact-seed
unfolded integral using its genuine L2 representative identities. -/
theorem quotientTensorPoincareL2_inner_eq_seed_pairing (N : ℕ) [NeZero N] {ι κ : Type*}
    (s : Finset ι) (T : ι → CompactTensor) (t : Finset κ) (U : κ → CompactTensor) :
    inner ℂ (quotientTensorPoincareL2 N s T) (quotientTensorPoincareL2 N t U) =
      ∫ z : UpperHalfPlane, star (finiteCoreFunction s T z) * finiteCompactTensorPoincare N t U z := by
  rw [← quotient_poincare_pairing_unfolding N s T t U, L2.inner_def]
  apply integral_congr_ae
  have hs := (quotientTensorPoincare_memLp_two N s T).coeFn_toLp
  have ht := (quotientTensorPoincare_memLp_two N t U).coeFn_toLp
  filter_upwards [hs, ht] with q hqS hqT
  rw [hqS, hqT]
  simp only [RCLike.inner_apply', Complex.star_def]

end
end ImbalancedChen.Part3.Gamma0PoincarePairingUnfolding20261025a
