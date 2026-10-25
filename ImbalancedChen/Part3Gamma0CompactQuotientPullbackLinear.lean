import ImbalancedChen.Part3Gamma0CompactQuotientLocalLp
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Operator.Basic

/-! SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
The actual compact quotient pullback is a bounded complex linear map,
with its bound supplied by actual compact proper-action unfolding.
This is local on K and makes no global upper-half-plane L2 assertion. -/

namespace ImbalancedChen.Part3.Gamma0CompactQuotientPullbackLinear20261025a
noncomputable section
open Set Filter MeasureTheory
open scoped UpperHalfPlane
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
open ImbalancedChen.Part3.Gamma0CompactGlobalOverlap20261025a
open ImbalancedChen.Part3.Gamma0CompactQuotientMeasureDomination20261025a
open ImbalancedChen.Part3.Gamma0CompactQuotientLocalLp20261025a

abbrev LocalScalarL2 (K : Set UpperHalfPlane) :=
  Lp ℂ 2 ((volume : Measure UpperHalfPlane).restrict K)

def compactPullbackL2 (N : ℕ) [NeZero N] {K : Set UpperHalfPlane} (hK : IsCompact K)
    (f : Lp ℂ 2 (carrierPushforward N)) : LocalScalarL2 K :=
  (quotientLp_pullback_memLp N hK f).toLp (fun z => f (orbitProjection N z))

theorem compactPullbackL2_coe_ae (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) (f : Lp ℂ 2 (carrierPushforward N)) :
    (compactPullbackL2 N hK f : UpperHalfPlane → ℂ) =ᵐ[(volume : Measure UpperHalfPlane).restrict K]
      (fun z => f (orbitProjection N z)) :=
  (quotientLp_pullback_memLp N hK f).coeFn_toLp

def compactPullbackLinear (N : ℕ) [NeZero N] {K : Set UpperHalfPlane} (hK : IsCompact K) :
    Lp ℂ 2 (carrierPushforward N) →ₗ[ℂ] LocalScalarL2 K where
  toFun := compactPullbackL2 N hK
  map_add' f g := by
    apply Lp.ext
    have hsum := quotient_ae_eq_pullback_compact N hK (Lp.coeFn_add f g)
    filter_upwards [compactPullbackL2_coe_ae N hK (f+g),
      compactPullbackL2_coe_ae N hK f,compactPullbackL2_coe_ae N hK g,
      Lp.coeFn_add (compactPullbackL2 N hK f) (compactPullbackL2 N hK g),hsum]
      with z hz hf hg hfg hsumz
    rw [hz,hfg]
    simpa only [Pi.add_apply,hf,hg] using hsumz
  map_smul' c f := by
    apply Lp.ext
    have hsmul := quotient_ae_eq_pullback_compact N hK (Lp.coeFn_smul c f)
    filter_upwards [compactPullbackL2_coe_ae N hK (c • f),compactPullbackL2_coe_ae N hK f,
      Lp.coeFn_smul c (compactPullbackL2 N hK f),hsmul] with z hz hf hcf hsmulz
    rw [hz,hcf]
    simpa only [Pi.smul_apply,hf] using hsmulz

private theorem scalar_integral_norm_sq {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : Lp ℂ 2 μ) : (∫ x, ‖f x‖^2 ∂μ) = ‖f‖^2 := by
  apply Complex.ofRealLI.injective
  simpa [← LinearIsometry.integral_comp_comm,inner_self_eq_norm_sq_to_K] using
    (L2.inner_def (𝕜 := ℂ) f f).symm

theorem compactPullbackLinear_bound (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) (f : Lp ℂ 2 (carrierPushforward N)) :
    ‖compactPullbackLinear N hK f‖ ≤ Real.sqrt (compactOverlapBound N K : ℝ)*‖f‖ := by
  have hnorm : ‖compactPullbackL2 N hK f‖^2 = ∫ z in K, ‖f (orbitProjection N z)‖^2 := by
    rw [← scalar_integral_norm_sq]
    apply integral_congr_ae
    exact (compactPullbackL2_coe_ae N hK f).mono (fun z hz => by rw [hz])
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg _)]
  change ‖compactPullbackL2 N hK f‖^2 ≤ _
  rw [hnorm,← scalar_integral_norm_sq (carrierPushforward N) f]
  exact quotientL2_compact_integral_sq_le N hK f

def compactPullbackCLM (N : ℕ) [NeZero N] {K : Set UpperHalfPlane} (hK : IsCompact K) :
    Lp ℂ 2 (carrierPushforward N) →L[ℂ] LocalScalarL2 K :=
  (compactPullbackLinear N hK).mkContinuous (Real.sqrt (compactOverlapBound N K : ℝ))
    (compactPullbackLinear_bound N hK)

end
end ImbalancedChen.Part3.Gamma0CompactQuotientPullbackLinear20261025a
