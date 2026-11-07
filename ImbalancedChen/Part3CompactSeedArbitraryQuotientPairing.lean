import ImbalancedChen.Part3Gamma0CompactQuotientLocalLp
import ImbalancedChen.Part3GammaCompactSeedL2Transport
import ImbalancedChen.Part3ActualPoincareSpectralCoefficient

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Native full effective Gamma0 unfolding of one arbitrary continuous compact
seed against an arbitrary actual quotient L2 vector. Compact local quotient
L2, finite compact volume and seed boundedness derive the TRUE seed pair L1.
The effective center is counted once. No continuous quotient representative,
target pairing identity, absolute-series bound, or spectral basis is assumed.
-/
namespace ImbalancedChen.Part3.CompactSeedArbitraryQuotientPairing20261026b
noncomputable section
open Set MeasureTheory Filter
open scoped UpperHalfPlane
open Gamma0QuotientCellPushforward20261025a Gamma0CompactQuotientLocalLp20261025a
open Gamma0CarrierAESection20261025a Gamma0CarrierMeasurableInverse20261025a
open Gamma0QuotientConullTransport20261025a Gamma0EffectiveActionKernel20261024z
open Gamma0EffectiveFiniteUnfolding20261025a Gamma0ComplexL1PoincareUnfolding20261025a
open GammaCompactSeedL2Transport20261026a ActualPoincareSpectralCoefficient20261026a

theorem compact_seed_testLift_pair_integrable (N : ℕ) [NeZero N]
    (f : UpperHalfPlane → ℂ) (hf : Continuous f) {K : Set UpperHalfPlane}
    (hK : IsCompact K) (hs : Function.support f ⊆ K)
    (U : Gamma0OrbitSpace N → ℂ) (hU : MemLp U 2 (carrierPushforward N)) :
    Integrable (fun z => star (f z) * testLift N U z) (volume : Measure UpperHalfPlane) := by
  letI : IsFiniteMeasure ((volume : Measure UpperHalfPlane).restrict K) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hK.measure_lt_top⟩
  have hu : IntegrableOn (testLift N U) K :=
    (quotient_memLp_pullback_compact N hK hU).integrable (by norm_num)
  have hp : IntegrableOn (fun z => star (f z) * testLift N U z) K :=
    IntegrableOn.continuousOn_mul hf.star.continuousOn hu hK
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp hp
  intro z hz
  exact hs (fun hfz => hz (by simp [hfz]))

theorem compact_pair_full_trace (N : ℕ) (f : UpperHalfPlane → ℂ)
    (U : Gamma0OrbitSpace N → ℂ) (z : UpperHalfPlane) :
    complexSeedTrace N (fun w => star (f w) * testLift N U w) z =
      star (complexSeedTrace N f z) * testLift N U z := by
  unfold complexSeedTrace translatedSeed
  calc
    _ = ∑' q : effectiveGamma0 N,
        star (f (effectiveMatrixAction N q z)) * testLift N U z := by
      apply tsum_congr
      intro q
      rw [show testLift N U (effectiveMatrixAction N q z) = testLift N U z from
        testLift_invariant N U (effectiveRepresentative N q) z]
    _ = _ := by rw [tsum_mul_right,← tsum_star]

theorem compact_seed_quotient_pairing_unfolding (N : ℕ) [NeZero N]
    (f : UpperHalfPlane → ℂ) (hf : Continuous f) {K : Set UpperHalfPlane}
    (hK : IsCompact K) (hs : Function.support f ⊆ K)
    (U : Gamma0OrbitSpace N → ℂ) (hU : MemLp U 2 (carrierPushforward N)) :
    (∫ q, star (complexPoincare N f q) * U q ∂carrierPushforward N) =
      ∫ z : UpperHalfPlane, star (f z) * testLift N U z := by
  calc
    _ = ∫ z : reducedCarrier N, star (complexSeedTrace N f z) * testLift N U z
        ∂reducedCarrierMeasure N := by
      rw [← reducedProjection_map_measure N,
        (reducedProjection_measurableEmbedding N).integral_map]
      apply integral_congr_ae
      exact Eventually.of_forall (fun z => by rw [complexPoincare_projection]; rfl)
    _ = ∫ z in reducedCarrier N,
        complexSeedTrace N (fun w => star (f w) * testLift N U w) z := by
      rw [integral_subtype_comap (reducedCarrier_measurable N)]
      apply integral_congr_ae
      exact Eventually.of_forall (fun z => (compact_pair_full_trace N f U z).symm)
    _ = _ := complex_carrier_unfolding N _
      (compact_seed_testLift_pair_integrable N f hf hK hs U hU)

/-- Literal native Hilbert identity for the actual compact seed vector,
with both quotient L2 representatives produced by their original APIs. -/
theorem compact_seedL2_inner_eq_seed_pairing (N : ℕ) [NeZero N]
    (f : UpperHalfPlane → ℂ) (hf : Continuous f) (K : Set UpperHalfPlane)
    (hK : IsCompact K) (hs : Function.support f ⊆ K)
    (V : Lp ℂ 2 (carrierPushforward N)) :
    inner ℂ (seedL2 N f hf K hK hs) V =
      ∫ z : UpperHalfPlane, star (f z) * testLift N V z := by
  rw [← compact_seed_quotient_pairing_unfolding N f hf hK hs V V.memLp,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [seedL2_ae N f hf K hK hs] with q hq
  rw [hq]
  simp only [RCLike.inner_apply',Complex.star_def]

end
end ImbalancedChen.Part3.CompactSeedArbitraryQuotientPairing20261026b
