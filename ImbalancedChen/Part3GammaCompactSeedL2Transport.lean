import ImbalancedChen.Part3Gamma0CompactSeedSharpL2Budget
import ImbalancedChen.Part3Gamma0CompactSeedQuotientL2Budget
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

Quantitative transfer from a common compact H support to the ACTUAL Gamma0
quotient L2. The constant uses the genuine effective-group compact overlap
and the original finite quotient measure. All translated sums are finite
by properness before linearity is applied. This is seed approximation
transport; no core membership or convergence target is a premise.
-/

namespace ImbalancedChen.Part3.GammaCompactSeedL2Transport20261026a

noncomputable section
open Set Filter MeasureTheory
open scoped UpperHalfPlane ENNReal
open Gamma0EffectiveActionKernel20261024z Gamma0EffectiveFiniteUnfolding20261025a
open Gamma0CompactTensorPoincareLocalFinite20261025a
open Gamma0CompactGlobalOverlap20261025a Gamma0CompactSeedSharpL2Budget20261025a
open Gamma0ComplexL1PoincareUnfolding20261025a Gamma0CompactSeedQuotientL2Budget20261025a
open Gamma0QuotientCellPushforward20261025a Gamma0CarrierAESection20261025a
open Gamma0QuotientConullTransport20261025a Gamma0CarrierMeasurableInverse20261025a

local instance quotientFinite (N : ℕ) [NeZero N] : IsFiniteMeasure (carrierPushforward N) :=
  ⟨carrierPushforward_finite N⟩

/-- Original quotient volume factor in the pinned Lp uniform-bound theorem. -/
def quotientL2MassFactor (N : ℕ) [NeZero N] : ℝ :=
  (measureUnivNNReal (carrierPushforward N) : ℝ) ^ ((2 : ℝ≥0∞).toReal)⁻¹

def transportConstant (N : ℕ) [NeZero N] (K : Set UpperHalfPlane) : ℝ :=
  quotientL2MassFactor N * (compactOverlapBound N K : ℝ)

theorem transportConstant_nonneg (N : ℕ) [NeZero N] (K : Set UpperHalfPlane) :
    0 ≤ transportConstant N K := by
  unfold transportConstant quotientL2MassFactor
  positivity

theorem sub_support_subset {f g : UpperHalfPlane → ℂ} {K : Set UpperHalfPlane}
    (hf : Function.support f ⊆ K) (hg : Function.support g ⊆ K) :
    Function.support (f - g) ⊆ K := by
  intro z hz
  by_cases hzf : f z = 0
  · apply hg
    intro hzg
    exact hz (by simp [hzf, hzg])
  · exact hf hzf

/-- The precise compact-overlap constant works for every prescribed seed
ceiling, rather than a supremum chosen separately for every approximant. -/
theorem compactTrace_uniform_bound (N : ℕ) (f : UpperHalfPlane → ℂ)
    {K : Set UpperHalfPlane} (hK : IsCompact K) (hs : Function.support f ⊆ K)
    {epsilon : ℝ} (he : 0 ≤ epsilon) (hb : ∀ z ∈ K, ‖f z‖ ≤ epsilon)
    (z : UpperHalfPlane) :
    ‖complexSeedTrace N f z‖ ≤ (compactOverlapBound N K : ℝ) * epsilon := by
  obtain ⟨S, hcard, hzero, hsum, _⟩ := compactSeed_finite_cauchy N f hK hs z
  have hterm : ∀ q, ‖translatedSeed N f q z‖ ≤ epsilon := by
    intro q
    by_cases hz : translatedSeed N f q z = 0
    · simpa only [hz, norm_zero] using he
    · exact hb _ (hs hz)
  calc
    ‖complexSeedTrace N f z‖ = ‖∑ q ∈ S, translatedSeed N f q z‖ := by rw [hsum]
    _ ≤ ∑ q ∈ S, ‖translatedSeed N f q z‖ := norm_sum_le _ _
    _ ≤ ∑ _q ∈ S, epsilon := Finset.sum_le_sum (fun q _ => hterm q)
    _ = (S.card : ℝ) * epsilon := by simp
    _ ≤ (compactOverlapBound N K : ℝ) * epsilon :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) he

theorem compactQuotient_uniform_bound (N : ℕ) [NeZero N]
    (f : UpperHalfPlane → ℂ) {K : Set UpperHalfPlane}
    (hK : IsCompact K) (hs : Function.support f ⊆ K)
    {epsilon : ℝ} (he : 0 ≤ epsilon) (hb : ∀ z ∈ K, ‖f z‖ ≤ epsilon)
    (q : Gamma0OrbitSpace N) :
    ‖complexPoincare N f q‖ ≤ (compactOverlapBound N K : ℝ) * epsilon := by
  by_cases hq : q ∈ range (reducedProjection N)
  · obtain ⟨z, rfl⟩ := hq
    rw [complexPoincare_projection]
    exact compactTrace_uniform_bound N f hK hs he hb z
  · rw [complexPoincare_off_section N f hq, norm_zero]
    exact mul_nonneg (Nat.cast_nonneg _) he

/-- Genuine L2 class on the original quotient measure. -/
def seedL2 (N : ℕ) [NeZero N] (f : UpperHalfPlane → ℂ) (hf : Continuous f)
    (K : Set UpperHalfPlane) (hK : IsCompact K) (hs : Function.support f ⊆ K) :
    Lp ℂ 2 (carrierPushforward N) :=
  (compactPoincare_memLp_two N f hf hK hs).toLp (complexPoincare N f)

theorem seedL2_ae (N : ℕ) [NeZero N] (f : UpperHalfPlane → ℂ) (hf : Continuous f)
    (K : Set UpperHalfPlane) (hK : IsCompact K) (hs : Function.support f ⊆ K) :
    (seedL2 N f hf K hK hs : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
      complexPoincare N f :=
  (compactPoincare_memLp_two N f hf hK hs).coeFn_toLp

theorem seedL2_norm_bound (N : ℕ) [NeZero N]
    (f : UpperHalfPlane → ℂ) (hf : Continuous f) (K : Set UpperHalfPlane)
    (hK : IsCompact K) (hs : Function.support f ⊆ K)
    {epsilon : ℝ} (he : 0 ≤ epsilon) (hb : ∀ z ∈ K, ‖f z‖ ≤ epsilon) :
    ‖seedL2 N f hf K hK hs‖ ≤ transportConstant N K * epsilon := by
  have hbound : ∀ᵐ q ∂carrierPushforward N,
      ‖seedL2 N f hf K hK hs q‖ ≤ (compactOverlapBound N K : ℝ) * epsilon := by
    filter_upwards [seedL2_ae N f hf K hK hs] with q hq
    rw [hq]
    exact compactQuotient_uniform_bound N f hK hs he hb q
  simpa only [transportConstant, quotientL2MassFactor, mul_assoc] using
    (Lp.norm_le_of_ae_bound (mul_nonneg (Nat.cast_nonneg _) he) hbound)

private theorem compact_seed_summable (N : ℕ) (f : UpperHalfPlane → ℂ)
    {K : Set UpperHalfPlane} (hK : IsCompact K) (hs : Function.support f ⊆ K)
    (z : UpperHalfPlane) :
    Summable (fun q : effectiveGamma0 N => f (effectiveMatrixAction N q z)) := by
  obtain ⟨U, hU, S, hS⟩ := compact_seed_locally_finite N f hK hs z
  exact summable_of_ne_finset_zero (s := S)
    (fun q hq => hS z (mem_of_mem_nhds hU) q hq)

theorem compactTrace_sub (N : ℕ) (f g : UpperHalfPlane → ℂ)
    {K : Set UpperHalfPlane} (hK : IsCompact K)
    (hf : Function.support f ⊆ K) (hg : Function.support g ⊆ K) :
    complexSeedTrace N (f - g) = complexSeedTrace N f - complexSeedTrace N g := by
  funext z
  exact (compact_seed_summable N f hK hf z).tsum_sub
    (compact_seed_summable N g hK hg z)

/-- Linearity is established on the actual conull reduced section. -/
theorem compactQuotient_sub_ae (N : ℕ) [NeZero N] (f g : UpperHalfPlane → ℂ)
    {K : Set UpperHalfPlane} (hK : IsCompact K)
    (hf : Function.support f ⊆ K) (hg : Function.support g ⊆ K) :
    complexPoincare N (f - g) =ᵐ[carrierPushforward N]
      complexPoincare N f - complexPoincare N g := by
  filter_upwards [reducedProjection_range_ae N] with q hq
  obtain ⟨z, rfl⟩ := hq
  simp only [Pi.sub_apply, complexPoincare_projection,
    compactTrace_sub N f g hK hf hg]

theorem seedL2_sub (N : ℕ) [NeZero N] (f g : UpperHalfPlane → ℂ)
    (hf : Continuous f) (hg : Continuous g) (K : Set UpperHalfPlane)
    (hK : IsCompact K) (hfs : Function.support f ⊆ K) (hgs : Function.support g ⊆ K) :
    seedL2 N (f - g) (hf.sub hg) K hK (sub_support_subset hfs hgs) =
      seedL2 N f hf K hK hfs - seedL2 N g hg K hK hgs := by
  apply Lp.ext
  filter_upwards [seedL2_ae N (f-g) (hf.sub hg) K hK (sub_support_subset hfs hgs),
    seedL2_ae N f hf K hK hfs, seedL2_ae N g hg K hK hgs,
    compactQuotient_sub_ae N f g hK hfs hgs,
    Lp.coeFn_sub (seedL2 N f hf K hK hfs) (seedL2 N g hg K hK hgs)]
    with q hsub hfa hga htrace hlp
  simp only [Pi.sub_apply] at htrace
  rw [hsub, hlp, hfa, hga]
  exact htrace

/-- The SAME compact support controls every member of an approximation
family. The right-hand constant is independent of both seeds and epsilon. -/
theorem seedL2_difference_bound (N : ℕ) [NeZero N] (f g : UpperHalfPlane → ℂ)
    (hf : Continuous f) (hg : Continuous g) (K : Set UpperHalfPlane)
    (hK : IsCompact K) (hfs : Function.support f ⊆ K) (hgs : Function.support g ⊆ K)
    {epsilon : ℝ} (he : 0 ≤ epsilon)
    (herr : ∀ z ∈ K, ‖f z - g z‖ ≤ epsilon) :
    ‖seedL2 N f hf K hK hfs - seedL2 N g hg K hK hgs‖ ≤
      transportConstant N K * epsilon := by
  rw [← seedL2_sub]
  exact seedL2_norm_bound N (f-g) (hf.sub hg) K hK
    (sub_support_subset hfs hgs) he herr

end
end ImbalancedChen.Part3.GammaCompactSeedL2Transport20261026a
