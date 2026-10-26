import ImbalancedChen.Part3Gamma0ActualAdjointInteriorWeakEquation
import ImbalancedChen.Part3GammaCompactSeedL2Transport

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
One arbitrary compact continuous H seed paired with an arbitrary actual
quotient L2 vector. Compact local pullback L2 proves the product L1.
The full effective Gamma0 trace is unfolded; no support-in-carrier
reconstruction is used. In particular the seed may cross every cell seam.
-/

namespace ImbalancedChen.Part3.Gamma0CompactSeedL2PairingUnfolding20261026b
noncomputable section
open Set Function Filter MeasureTheory
open scoped UpperHalfPlane
open Gamma0EffectiveActionKernel20261024z Gamma0EffectiveFiniteUnfolding20261025a
open Gamma0QuotientCellPushforward20261025a Gamma0CarrierAESection20261025a
open Gamma0CarrierMeasurableInverse20261025a Gamma0QuotientConullTransport20261025a
open Gamma0ComplexL1PoincareUnfolding20261025a GammaCompactSeedL2Transport20261026a
open Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualAdjointInteriorWeakEquation20261025a

/-- The raw orbit representative is exactly invariant, before any AE
or local regularity argument and for arbitrary quotient functions. -/
theorem orbit_pullback_effective_invariant (N : ℕ)
    (F : Gamma0OrbitSpace N → ℂ) (q : effectiveGamma0 N) (z : UpperHalfPlane) :
    F (orbitProjection N (effectiveMatrixAction N q z)) = F (orbitProjection N z) := by
  rw [effectiveMatrixAction, orbitProjection_smul]

/-- Factorization uses the full effective-group trace, including all
translates meeting the compact seed; no translate is deleted. -/
theorem compact_pair_trace (N : ℕ) (a : UpperHalfPlane → ℂ)
    (F : Gamma0OrbitSpace N → ℂ) (z : UpperHalfPlane) :
    complexSeedTrace N (fun w => star (a w) * F (orbitProjection N w)) z =
      star (complexSeedTrace N a z) * F (orbitProjection N z) := by
  unfold complexSeedTrace translatedSeed
  calc
    _ = ∑' q : effectiveGamma0 N,
        star (a (effectiveMatrixAction N q z)) * F (orbitProjection N z) := by
      apply tsum_congr
      intro q
      rw [orbit_pullback_effective_invariant]
    _ = _ := by rw [tsum_mul_right, ← tsum_star]

/-- Every genuine quotient L2 representative admits compact-seed
unfolding, without smoothness or boundedness of that representative. -/
theorem compact_seed_pairing_unfolding (N : ℕ) [NeZero N]
    (a : UpperHalfPlane → ℂ) (ha : Continuous a)
    {K : Set UpperHalfPlane} (hK : IsCompact K) (hs : Function.support a ⊆ K)
    (f : QuotientL2 N) :
    (∫ q, star (complexPoincare N a q) * f q ∂carrierPushforward N) =
      ∫ z : UpperHalfPlane, star (a z) * f (orbitProjection N z) := by
  have hprod := compact_seed_quotient_product_integrable N a ha hK hs f
  calc
    _ = ∫ z : reducedCarrier N,
        star (complexSeedTrace N a z) * f (reducedProjection N z)
          ∂reducedCarrierMeasure N := by
      rw [← reducedProjection_map_measure N,
        (reducedProjection_measurableEmbedding N).integral_map]
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by rw [complexPoincare_projection]
    _ = ∫ z in reducedCarrier N,
        star (complexSeedTrace N a z) * f (orbitProjection N z) :=
      integral_subtype_comap (reducedCarrier_measurable N) _
    _ = ∫ z in reducedCarrier N,
        complexSeedTrace N (fun w => star (a w) * f (orbitProjection N w)) z := by
      apply integral_congr_ae
      exact Eventually.of_forall fun z => (compact_pair_trace N a f z).symm
    _ = _ := complex_carrier_unfolding N _ hprod

/-- Representation-independent Hilbert endpoint. No pointwise equality
between a Poincare sum and its single seed is asserted. -/
theorem compact_seed_L2_inner (N : ℕ) [NeZero N]
    (a : UpperHalfPlane → ℂ) (ha : Continuous a)
    {K : Set UpperHalfPlane} (hK : IsCompact K) (hs : Function.support a ⊆ K)
    (A f : QuotientL2 N)
    (hA : (A : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N] complexPoincare N a) :
    inner ℂ A f = ∫ z : UpperHalfPlane, star (a z) * f (orbitProjection N z) := by
  rw [← compact_seed_pairing_unfolding N a ha hK hs f, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hA] with q hq
  rw [hq]
  simp only [RCLike.inner_apply', Complex.star_def]

theorem seedL2_inner (N : ℕ) [NeZero N]
    (a : UpperHalfPlane → ℂ) (ha : Continuous a)
    (K : Set UpperHalfPlane) (hK : IsCompact K) (hs : Function.support a ⊆ K)
    (f : QuotientL2 N) :
    inner ℂ (seedL2 N a ha K hK hs) f =
      ∫ z : UpperHalfPlane, star (a z) * f (orbitProjection N z) :=
  compact_seed_L2_inner N a ha hK hs _ f (seedL2_ae N a ha K hK hs)

end
end ImbalancedChen.Part3.Gamma0CompactSeedL2PairingUnfolding20261026b
