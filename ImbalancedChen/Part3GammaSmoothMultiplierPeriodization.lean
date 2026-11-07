import ImbalancedChen.Part3GammaFiniteTensorGraphCore
import ImbalancedChen.Part3ActualUpperMaassLinearity

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

A genuine Gamma0-invariant smooth multiplier may multiply a compact smooth
seed without any finite-tensor-span membership assumption. Actual effective
Poincare periodization commutes with that multiplier by proved actual-group
reindexing/invariance. The compact support remains the original seed's.
The resulting quotient input is genuinely L2, although the multiplier need
not be bounded on the noncompact quotient.
-/

namespace ImbalancedChen.Part3.GammaSmoothMultiplierPeriodization20261026a

noncomputable section
open Set MeasureTheory Filter
open scoped UpperHalfPlane
open MaassWeakOperatorCore20261024zz
open Gamma0EffectiveActionKernel20261024z Gamma0EffectiveFiniteUnfolding20261025a
open Gamma0CompactTensorPoincareLocalFinite20261025a
open Gamma0CompactTensorPoincareC2Core20261025a
open Gamma0ComplexL1PoincareUnfolding20261025a
open Gamma0QuotientCellPushforward20261025a Gamma0CarrierAESection20261025a
open Gamma0CarrierMeasurableInverse20261025a Gamma0QuotientConullTransport20261025a
open Gamma0CompactSeedQuotientL2Budget20261025a
open Gamma0SmoothCompactTensorCore20261025a
open GammaFiniteTensorGraphCore20261026a ActualCompactSeedMaassJoin20261025a

/-- Only actual group invariance is required, never a spectral multiplier. -/
abbrev IsGammaInvariant (N : ℕ) (chi : UpperHalfPlane → ℂ) : Prop :=
  ∀ gamma : CongruenceSubgroup.Gamma0 N, ∀ z, chi (gamma • z) = chi z

/-- Literal quotient multiplier on the SAME actual orbit space. -/
def quotientMultiplier (N : ℕ) (chi : UpperHalfPlane → ℂ)
    (hchi : IsGammaInvariant N chi) : Gamma0OrbitSpace N → ℂ :=
  Quotient.lift chi (by
    intro z w hzw
    obtain ⟨gamma, hgamma⟩ := MulAction.orbitRel_apply.mp hzw
    rw [← hgamma]
    exact hchi gamma w)

@[simp] theorem quotientMultiplier_projection (N : ℕ) (chi : UpperHalfPlane → ℂ)
    (hchi : IsGammaInvariant N chi) (z : UpperHalfPlane) :
    quotientMultiplier N chi hchi (orbitProjection N z) = chi z := rfl

theorem quotientMultiplier_measurable (N : ℕ) (chi : UpperHalfPlane → ℂ)
    (hchi : IsGammaInvariant N chi)
    (hs : ContDiffOn ℝ ∞ (extendUpper chi) positiveChart) :
    Measurable (quotientMultiplier N chi hchi) :=
  measurable_from_quotient.mpr (native_C2_continuous chi (hs.of_le (by simp))).measurable

theorem extendUpper_mul (chi f : UpperHalfPlane → ℂ) :
    extendUpper (chi * f) = extendUpper chi * extendUpper f := by
  funext p
  by_cases hp : 0 < p.2 <;> simp [extendUpper, hp]

theorem compact_multiplier_seed_smooth (chi f : UpperHalfPlane → ℂ)
    (hchi : ContDiffOn ℝ ∞ (extendUpper chi) positiveChart)
    (hf : ContDiffOn ℝ ∞ (extendUpper f) positiveChart) :
    ContDiffOn ℝ ∞ (extendUpper (chi*f)) positiveChart := by
  rw [extendUpper_mul]
  exact hchi.mul hf

theorem multiplier_seed_support_subset (chi f : UpperHalfPlane → ℂ) :
    Function.support (chi*f) ⊆ tsupport f := by
  intro z hz
  apply subset_tsupport
  intro hzero
  exact hz (by simp [hzero])

theorem multiplier_seed_hasCompactSupport (chi f : UpperHalfPlane → ℂ)
    (hfc : HasCompactSupport f) : HasCompactSupport (chi*f) :=
  HasCompactSupport.of_support_subset_isCompact hfc (multiplier_seed_support_subset chi f)

/-- Exact actual effective-group Poincare multiplier identity. No compact
or summability premise is hidden in this identity; multiplication by a fixed
complex scalar commutes with the total tsum operation. -/
theorem complexSeedTrace_mul_invariant (N : ℕ) (chi f : UpperHalfPlane → ℂ)
    (hchi : IsGammaInvariant N chi) :
    complexSeedTrace N (chi*f) = chi * complexSeedTrace N f := by
  funext z
  change (∑' q : effectiveGamma0 N,
      chi (effectiveMatrixAction N q z) * f (effectiveMatrixAction N q z)) =
    chi z * ∑' q : effectiveGamma0 N, f (effectiveMatrixAction N q z)
  calc
    _ = ∑' q : effectiveGamma0 N, chi z * f (effectiveMatrixAction N q z) := by
      apply tsum_congr
      intro q
      rw [show chi (effectiveMatrixAction N q z) = chi z from
        hchi (effectiveRepresentative N q) z]
    _ = _ := tsum_mul_left

/-- The quotient equality is literal everywhere: both seed sums are zero
off the canonical reduced-section image; on it the actual trace identity
applies. This does not substitute a whole-H L2 measure. -/
theorem complexPoincare_mul_invariant (N : ℕ) [NeZero N]
    (chi f : UpperHalfPlane → ℂ) (hchi : IsGammaInvariant N chi) :
    complexPoincare N (chi*f) =
      quotientMultiplier N chi hchi * complexPoincare N f := by
  funext q
  by_cases hq : q ∈ range (reducedProjection N)
  · obtain ⟨z, rfl⟩ := hq
    simp only [Pi.mul_apply, complexPoincare_projection]
    exact congrFun (complexSeedTrace_mul_invariant N chi f hchi) z
  · simp only [Pi.mul_apply, complexPoincare_off_section N (chi*f) hq,
      complexPoincare_off_section N f hq, mul_zero]

/-- A possibly globally unbounded smooth invariant multiplier gives an
actual L2 product here because the compact seed controls its periodization. -/
theorem multiplied_quotient_memLp (N : ℕ) [NeZero N]
    (chi f : UpperHalfPlane → ℂ) (hchi : IsGammaInvariant N chi)
    (hcs : ContDiffOn ℝ ∞ (extendUpper chi) positiveChart)
    (hfs : ContDiffOn ℝ ∞ (extendUpper f) positiveChart) (hfc : HasCompactSupport f) :
    MemLp (quotientMultiplier N chi hchi * complexPoincare N f) 2 (carrierPushforward N) := by
  rw [← complexPoincare_mul_invariant N chi f hchi]
  exact compactPoincare_memLp_two N (chi*f)
    (native_C2_continuous _ ((compact_multiplier_seed_smooth chi f hcs hfs).of_le (by simp)))
    hfc (multiplier_seed_support_subset chi f)

/-- Any actual compact smooth seed gives a legal multiplied minimal graph
pair, using the CONSTRUCTIVE finite tensor graph-core theorem. No claim is
made that the multiplied seed itself is a finite tensor sum. -/
theorem multiplied_seed_ae_pair_mem_minimalGraph
    (N : ℕ) [NeZero N] (chi f : UpperHalfPlane → ℂ)
    (hcs : ContDiffOn ℝ ∞ (extendUpper chi) positiveChart)
    (hfs : ContDiffOn ℝ ∞ (extendUpper f) positiveChart) (hfc : HasCompactSupport f)
    (u v : Lp ℂ 2 (carrierPushforward N))
    (hu : (u : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
      complexPoincare N (chi*f))
    (hv : (v : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
      complexPoincare N (upperMaass (chi*f))) :
    (u,v) ∈ (Gamma0ActualMaassClosedOperator20261025a.actualClosedGammaMaass N).graph :=
  compact_smooth_seed_ae_pair_mem_minimalGraph N (chi*f)
    (multiplier_seed_hasCompactSupport chi f hfc)
    (compact_multiplier_seed_smooth chi f hcs hfs) u v hu hv

/-- Original finite smooth Poincare seeds satisfy every analytic seed
condition needed above. This preserves the ORIGINAL factors and support. -/
theorem finiteSmoothSeed_compact_cinfty {ι : Type*} (s : Finset ι)
    (T : ι → SmoothCompactTensor) :
    HasCompactSupport (finiteCoreFunction s (fun i => (T i).toCompactTensor)) ∧
      ContDiffOn ℝ ∞
        (extendUpper (finiteCoreFunction s (fun i => (T i).toCompactTensor))) positiveChart := by
  constructor
  · exact HasCompactSupport.of_support_subset_isCompact
      (finiteCompactTensorSupportK_isCompact s (fun i => (T i).toCompactTensor))
      (finiteCoreFunction_support_subset s (fun i => (T i).toCompactTensor))
  · rw [extendUpper_finiteCoreFunction]
    exact (finiteSmoothChart_contDiff s T).contDiffOn

end
end ImbalancedChen.Part3.GammaSmoothMultiplierPeriodization20261026a
