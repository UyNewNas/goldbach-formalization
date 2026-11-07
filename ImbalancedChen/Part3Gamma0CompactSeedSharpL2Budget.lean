import ImbalancedChen.Part3Gamma0CompactGlobalOverlap
import ImbalancedChen.Part3Gamma0ComplexL1PoincareUnfolding
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.ENNReal.BigOperators

/-!
# Quantitative compact-seed Poincare squared-norm budget

SOURCE_WRITTEN / UNCOMPILED / NOT_ROOT_ACCEPTED.

The actual global overlap theorem supplies one finite multiplicity M at
every point of H. Finite Cauchy-Schwarz gives |P f|^2 <= M P(|f|^2).
The already proved actual nonnegative unfolding, with its effective central
kernel counted once, gives the sharp spatial squared-norm mass bound on
the concrete reduced carrier and the actual orbit quotient.

No absolute-series, target-L2, overlap or unfolding conclusion is supplied
as a premise. Squared masses use nonnegative extended integrals, so the
budget remains meaningful before seed finiteness is imposed. A finite
seed squared mass then gives a finite output squared mass explicitly.
-/

namespace ImbalancedChen.Part3.Gamma0CompactSeedSharpL2Budget20261025a
noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane Pointwise ENNReal
open ImbalancedChen.Part3.Gamma0EffectiveActionKernel20261024z
open ImbalancedChen.Part3.Gamma0EffectiveFiniteUnfolding20261025a
open ImbalancedChen.Part3.Gamma0CompactGlobalOverlap20261025a
open ImbalancedChen.Part3.Gamma0NonnegativePoincareUnfolding20261025a
open ImbalancedChen.Part3.Gamma0ComplexL1PoincareUnfolding20261025a
open ImbalancedChen.Part3.Gamma0CarrierAESection20261025a
open ImbalancedChen.Part3.Gamma0CarrierMeasurableInverse20261025a
open ImbalancedChen.Part3.Gamma0QuotientConullTransport20261025a
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a

/-- Actual finite-hit Cauchy-Schwarz, with the cardinality bound proved
from compact properness and chosen before the point z. -/
theorem compactSeed_finite_cauchy (N : ℕ) (f : UpperHalfPlane → ℂ)
    {K : Set UpperHalfPlane} (hK : IsCompact K) (hsupp : Function.support f ⊆ K)
    (z : UpperHalfPlane) :
    ∃ S : Finset (effectiveGamma0 N),
      S.card ≤ compactOverlapBound N K ∧
      (∀ q ∉ S, translatedSeed N f q z = 0) ∧
      complexSeedTrace N f z = ∑ q ∈ S, translatedSeed N f q z ∧
      ‖complexSeedTrace N f z‖ ^ 2 ≤
        (compactOverlapBound N K : ℝ) * ∑ q ∈ S, ‖translatedSeed N f q z‖ ^ 2 := by
  have hh := compact_hits_finite_and_card_le N hK z
  let S := hh.1.toFinset
  have hcard : S.card ≤ compactOverlapBound N K := by
    change hh.1.toFinset.card ≤ _
    rw [← Set.ncard_eq_toFinset_card (compactHitSet N K z) hh.1]
    exact hh.2.trans (Nat.le_succ _)
  have hzero : ∀ q ∉ S, translatedSeed N f q z = 0 := by
    intro q hq
    by_contra hnonzero
    exact hq (hh.1.mem_toFinset.mpr (hsupp hnonzero))
  have htrace : complexSeedTrace N f z = ∑ q ∈ S, translatedSeed N f q z :=
    tsum_eq_sum hzero
  refine ⟨S, hcard, hzero, htrace, ?_⟩
  rw [htrace]
  have hnorm := norm_sum_le S (fun q => translatedSeed N f q z)
  have hsq : ‖∑ q ∈ S, translatedSeed N f q z‖ ^ 2 ≤
      (∑ q ∈ S, ‖translatedSeed N f q z‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have hCS : (∑ q ∈ S, ‖translatedSeed N f q z‖) ^ 2 ≤
      (S.card : ℝ) * ∑ q ∈ S, ‖translatedSeed N f q z‖ ^ 2 := by
    simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] using
      Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ))
        (fun q => ‖translatedSeed N f q z‖)
  exact (hsq.trans hCS).trans (mul_le_mul_of_nonneg_right
    (by exact_mod_cast hcard) (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

/-- The requested actual pointwise Poincare Cauchy inequality. The real
square-mass series is a genuine finite sum at every point, by compactness. -/
theorem compactSeed_pointwise_cauchy (N : ℕ) (f : UpperHalfPlane → ℂ)
    {K : Set UpperHalfPlane} (hK : IsCompact K) (hsupp : Function.support f ⊆ K)
    (z : UpperHalfPlane) :
    ‖complexSeedTrace N f z‖ ^ 2 ≤ (compactOverlapBound N K : ℝ) *
      ∑' q : effectiveGamma0 N, ‖translatedSeed N f q z‖ ^ 2 := by
  obtain ⟨S, _hcard, hzero, _htrace, hbound⟩ := compactSeed_finite_cauchy N f hK hsupp z
  have hsum : (∑' q : effectiveGamma0 N, ‖translatedSeed N f q z‖ ^ 2) =
      ∑ q ∈ S, ‖translatedSeed N f q z‖ ^ 2 := by
    apply tsum_eq_sum
    intro q hq
    simp only [hzero q hq, norm_zero, zero_pow (by decide : 2 ≠ 0)]
  simpa only [hsum] using hbound

def seedSquareMass (f : UpperHalfPlane → ℂ) (z : UpperHalfPlane) : ℝ≥0∞ :=
  ENNReal.ofReal (‖f z‖ ^ 2)

theorem seedSquareMass_measurable (f : UpperHalfPlane → ℂ) (hf : Measurable f) :
    Measurable (seedSquareMass f) := by
  unfold seedSquareMass
  fun_prop

/-- Pointwise nonnegative majorant suitable for the exact actual
unfolding theorem; it is proved from the finite Cauchy inequality. -/
theorem compactSeed_pointwise_squareMass_majorant (N : ℕ) (f : UpperHalfPlane → ℂ)
    {K : Set UpperHalfPlane} (hK : IsCompact K) (hsupp : Function.support f ⊆ K)
    (z : UpperHalfPlane) :
    ENNReal.ofReal (‖complexSeedTrace N f z‖ ^ 2) ≤
      ENNReal.ofReal (compactOverlapBound N K : ℝ) * fullSeedTrace N (seedSquareMass f) z := by
  obtain ⟨S, _hcard, hzero, _htrace, hbound⟩ := compactSeed_finite_cauchy N f hK hsupp z
  have hsum : fullSeedTrace N (seedSquareMass f) z =
      ∑ q ∈ S, ENNReal.ofReal (‖translatedSeed N f q z‖ ^ 2) := by
    apply tsum_eq_sum
    intro q hq
    change ENNReal.ofReal (‖translatedSeed N f q z‖ ^ 2) = 0
    simp only [hzero q hq, norm_zero, zero_pow (by decide : 2 ≠ 0), ENNReal.ofReal_zero]
  calc
    _ ≤ ENNReal.ofReal ((compactOverlapBound N K : ℝ) *
        ∑ q ∈ S, ‖translatedSeed N f q z‖ ^ 2) := ENNReal.ofReal_le_ofReal hbound
    _ = ENNReal.ofReal (compactOverlapBound N K : ℝ) *
        ∑ q ∈ S, ENNReal.ofReal (‖translatedSeed N f q z‖ ^ 2) := by
      rw [ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
    _ = _ := by rw [hsum]

/-- Sharp actual reduced-carrier squared-norm budget. Its constant is
exactly the proved global compact multiplicity, independent of z. -/
theorem compactSeed_carrier_squareMass_budget (N : ℕ) [NeZero N]
    (f : UpperHalfPlane → ℂ) (hf : Measurable f)
    {K : Set UpperHalfPlane} (hK : IsCompact K) (hsupp : Function.support f ⊆ K) :
    (∫⁻ z in reducedCarrier N, ENNReal.ofReal (‖complexSeedTrace N f z‖ ^ 2)) ≤
      ENNReal.ofReal (compactOverlapBound N K : ℝ) *
        ∫⁻ z, seedSquareMass f z ∂(volume : Measure UpperHalfPlane) := by
  calc
    _ ≤ ∫⁻ z in reducedCarrier N,
        ENNReal.ofReal (compactOverlapBound N K : ℝ) * fullSeedTrace N (seedSquareMass f) z :=
      lintegral_mono (compactSeed_pointwise_squareMass_majorant N f hK hsupp)
    _ = ENNReal.ofReal (compactOverlapBound N K : ℝ) *
        ∫⁻ z in reducedCarrier N, fullSeedTrace N (seedSquareMass f) z :=
      lintegral_const_mul _ (fullSeedTrace_measurable N _ (seedSquareMass_measurable f hf))
    _ = _ := by rw [← lintegral_fullSeedTrace N _ (seedSquareMass_measurable f hf)]

/-- Exact section transport of squared mass; no quotient-L2 property is
assumed to justify it. It uses the actual measurable reduced-carrier map. -/
theorem quotient_squareMass_eq_carrier (N : ℕ) [NeZero N]
    (f : UpperHalfPlane → ℂ) :
    (∫⁻ u, ENNReal.ofReal (‖complexPoincare N f u‖ ^ 2) ∂carrierPushforward N) =
      ∫⁻ z in reducedCarrier N, ENNReal.ofReal (‖complexSeedTrace N f z‖ ^ 2) := by
  calc
    _ = ∫⁻ z : reducedCarrier N,
        ENNReal.ofReal (‖complexPoincare N f (reducedProjection N z)‖ ^ 2)
          ∂reducedCarrierMeasure N := by
      rw [← reducedProjection_map_measure N,
        (reducedProjection_measurableEmbedding N).lintegral_map]
    _ = ∫⁻ z : reducedCarrier N, ENNReal.ofReal (‖complexSeedTrace N f z‖ ^ 2)
        ∂reducedCarrierMeasure N := by
      apply lintegral_congr
      intro z
      rw [complexPoincare_projection N f z]
    _ = _ := lintegral_subtype_comap (reducedCarrier_measurable N) _

/-- Sharp squared-norm mass budget for the ACTUAL complex quotient
Poincare series, not for a whole-plane surrogate or an abstract trace. -/
theorem compactSeed_quotient_squareMass_budget (N : ℕ) [NeZero N]
    (f : UpperHalfPlane → ℂ) (hf : Measurable f)
    {K : Set UpperHalfPlane} (hK : IsCompact K) (hsupp : Function.support f ⊆ K) :
    (∫⁻ u, ENNReal.ofReal (‖complexPoincare N f u‖ ^ 2) ∂carrierPushforward N) ≤
      ENNReal.ofReal (compactOverlapBound N K : ℝ) *
        ∫⁻ z, seedSquareMass f z ∂(volume : Measure UpperHalfPlane) := by
  rw [quotient_squareMass_eq_carrier]
  exact compactSeed_carrier_squareMass_budget N f hf hK hsupp

/-- A finite ORIGINAL seed square mass forces a finite actual quotient
output mass; the output L2 conclusion is not a premise. -/
theorem compactSeed_quotient_squareMass_finite (N : ℕ) [NeZero N]
    (f : UpperHalfPlane → ℂ) (hf : Measurable f)
    {K : Set UpperHalfPlane} (hK : IsCompact K) (hsupp : Function.support f ⊆ K)
    (hseed : (∫⁻ z, seedSquareMass f z ∂(volume : Measure UpperHalfPlane)) < ∞) :
    (∫⁻ u, ENNReal.ofReal (‖complexPoincare N f u‖ ^ 2) ∂carrierPushforward N) < ∞ :=
  (compactSeed_quotient_squareMass_budget N f hf hK hsupp).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hseed)

end
end ImbalancedChen.Part3.Gamma0CompactSeedSharpL2Budget20261025a
