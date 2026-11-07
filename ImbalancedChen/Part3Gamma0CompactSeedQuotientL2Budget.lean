import ImbalancedChen.Part3Gamma0CompactLaplacianSeed
import ImbalancedChen.Part3Gamma0CompactGlobalOverlap
import ImbalancedChen.Part3Gamma0ComplexL1PoincareUnfolding
import ImbalancedChen.Part3Gamma0CompactTensorQuotientL2Core

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The missing output L2 for the actual finite tensor Poincare core. The seed
finiteCoreLaplacian is only C0 compact; the generic compact-seed arguments
below require exactly that regularity. Actual proper-action global overlap
gives a uniform finite translate support, actual canonical complex L1
unfolding supplies AE strong measurability, and finite canonical quotient
mass gives L2. Neither hL2 nor hAbsSum is a supplied conclusion premise.

The output is the ACTUAL effective-Gamma0 Poincare series of the actual
second-order seed, on the existing genuine quotient section. Identification
with the geometric Delta of the input Poincare function requires the
independent true Mobius-Laplacian commutation theorem; it is not inferred
by relabeling the old whole-plane Maass operator. Input Poincare L2 was
already proved in CompactTensorQuotientL2Core and is not reproved here.
-/

namespace ImbalancedChen.Part3.Gamma0CompactSeedQuotientL2Budget20261025a

noncomputable section
open Set MeasureTheory Filter Topology
open scoped UpperHalfPlane Pointwise BigOperators
open ImbalancedChen.Part3.Gamma0EffectiveActionKernel20261024z
open ImbalancedChen.Part3.Gamma0EffectiveFiniteUnfolding20261025a
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
open ImbalancedChen.Part3.Gamma0CarrierAESection20261025a
open ImbalancedChen.Part3.Gamma0CarrierMeasurableInverse20261025a
open ImbalancedChen.Part3.Gamma0QuotientConullTransport20261025a
open ImbalancedChen.Part3.Gamma0ComplexL1PoincareUnfolding20261025a
open ImbalancedChen.Part3.Gamma0CompactTensorPoincareLocalFinite20261025a
open ImbalancedChen.Part3.Gamma0CompactTensorPoincareC2Core20261025a
open ImbalancedChen.Part3.Gamma0CompactGlobalOverlap20261025a
open ImbalancedChen.Part3.Gamma0CompactLaplacianSeed20261025a
open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz

theorem compactSeedTrace_continuous (N : ℕ) (f : UpperHalfPlane → ℂ)
    (hf : Continuous f) {K : Set UpperHalfPlane} (hK : IsCompact K)
    (hsupp : Function.support f ⊆ K) : Continuous (complexSeedTrace N f) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  obtain ⟨U, hU, S, hS⟩ := compact_seed_locally_finite N f hK hsupp z
  have hc : Continuous (fun w : UpperHalfPlane =>
      ∑ q ∈ S, f (effectiveMatrixAction N q w)) := by
    apply continuous_finsetSum S
    intro q _
    apply hf.comp
    change Continuous (fun w : UpperHalfPlane =>
      (SpecialLinearGroup.mapGL ℝ (effectiveRepresentative N q : SL(2, ℤ))) • w)
    exact continuous_const_smul _
  apply hc.continuousAt.congr_of_eventuallyEq
  apply Filter.eventually_of_mem hU
  intro w hw
  exact tsum_eq_sum (fun q hq => hS w hw q hq)

/-- Actual effective-group reindexing proves invariance for the C0 output
seed as well; it does not require that seed to be C2. -/
theorem compactSeedTrace_gamma0_invariant (N : ℕ) (f : UpperHalfPlane → ℂ)
    (gamma : CongruenceSubgroup.Gamma0 N) (z : UpperHalfPlane) :
    complexSeedTrace N f (gamma • z) = complexSeedTrace N f z := by
  unfold complexSeedTrace translatedSeed
  calc
    (∑' q : effectiveGamma0 N, f (effectiveMatrixAction N q (gamma • z))) =
        ∑' q : effectiveGamma0 N,
          f (effectiveMatrixAction N (q * QuotientGroup.mk gamma) z) := by
      apply tsum_congr
      intro q
      rw [← effectiveMatrixAction_mk_gamma N gamma z, ← effectiveMatrixAction_mul]
    _ = _ := (Equiv.mulRight (QuotientGroup.mk gamma : effectiveGamma0 N)).tsum_eq
      (fun q => f (effectiveMatrixAction N q z))

/-- Explicit finite-overlap/supremum budget for an arbitrary C0 compact
seed. The same M and B work at EVERY point of H and are derived here. -/
theorem compactSeedTrace_uniform_overlap_bound (N : ℕ) (f : UpperHalfPlane → ℂ)
    (hf : Continuous f) {K : Set UpperHalfPlane} (hK : IsCompact K)
    (hsupp : Function.support f ⊆ K) :
    ∃ M : ℕ, 0 < M ∧ ∃ B : ℝ, 0 ≤ B ∧
      (∀ z ∈ K, ‖f z‖ ≤ B) ∧
      ∀ z : UpperHalfPlane, ‖complexSeedTrace N f z‖ ≤ (M : ℝ) * B := by
  obtain ⟨M, hM, hfinite⟩ := compact_seed_uniform_finite_support N f hK hsupp
  obtain ⟨b, hb⟩ := hK.bddAbove_image hf.norm.continuousOn
  let B : ℝ := max b 0
  have hB : 0 ≤ B := le_max_right _ _
  have hbound : ∀ z ∈ K, ‖f z‖ ≤ B :=
    fun z hz => (hb ⟨z, hz, rfl⟩).trans (le_max_left _ _)
  refine ⟨M, hM, B, hB, hbound, ?_⟩
  intro z
  obtain ⟨S, hcard, hzero⟩ := hfinite z
  have hterm : ∀ q, ‖f (effectiveMatrixAction N q z)‖ ≤ B := by
    intro q
    by_cases hq : f (effectiveMatrixAction N q z) = 0
    · simpa only [hq, norm_zero] using hB
    · exact hbound _ (hsupp hq)
  calc
    ‖complexSeedTrace N f z‖ = ‖∑ q ∈ S, f (effectiveMatrixAction N q z)‖ :=
      congrArg norm (tsum_eq_sum (fun q hq => hzero q hq))
    _ ≤ ∑ q ∈ S, ‖f (effectiveMatrixAction N q z)‖ := norm_sum_le _ _
    _ ≤ ∑ _q ∈ S, B := Finset.sum_le_sum (fun q _ => hterm q)
    _ = (S.card : ℝ) * B := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (M : ℝ) * B := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hB

theorem compactSeed_integrable (f : UpperHalfPlane → ℂ) (hf : Continuous f)
    {K : Set UpperHalfPlane} (hK : IsCompact K) (hsupp : Function.support f ⊆ K) :
    Integrable f (volume : Measure UpperHalfPlane) := by
  have hc : HasCompactSupport f := by
    apply hK.of_isClosed_subset isClosed_closure
    exact closure_minimal hsupp hK.isClosed
  exact hf.integrable_of_hasCompactSupport hc

/-- The genuine quotient series is zero outside the actual section image;
on that image its terms are the actual translated C0 seed terms. -/
theorem complexPoincare_off_section (N : ℕ) [NeZero N] (f : UpperHalfPlane → ℂ)
    {u : Gamma0OrbitSpace N} (hu : u ∉ range (reducedProjection N)) :
    complexPoincare N f u = 0 := by
  unfold complexPoincare
  have hz : ∀ q : effectiveGamma0 N, quotientSeedTerm N f q u = 0 := by
    intro q
    exact Function.extend_apply' _ _ u hu
  simp only [hz, tsum_zero]

/-- Actual quotient L2 for any C0 compact seed, including the genuine
second-order output seed. All bounds are produced from compact geometry. -/
theorem compactPoincare_memLp_two (N : ℕ) [NeZero N] (f : UpperHalfPlane → ℂ)
    (hf : Continuous f) {K : Set UpperHalfPlane} (hK : IsCompact K)
    (hsupp : Function.support f ⊆ K) :
    MemLp (complexPoincare N f) 2 (carrierPushforward N) := by
  letI : IsFiniteMeasure (carrierPushforward N) := ⟨carrierPushforward_finite N⟩
  obtain ⟨M, _hM, B, hB, _hseed, hbound⟩ :=
    compactSeedTrace_uniform_overlap_bound N f hf hK hsupp
  apply MemLp.of_bound (complexPoincare_integrable N f
    (compactSeed_integrable f hf hK hsupp)).aestronglyMeasurable ((M : ℝ) * B)
  apply Filter.Eventually.of_forall
  intro u
  by_cases hu : u ∈ range (reducedProjection N)
  · obtain ⟨z, rfl⟩ := hu
    rw [complexPoincare_projection]
    exact hbound z
  · rw [complexPoincare_off_section N f hu, norm_zero]
    exact mul_nonneg (Nat.cast_nonneg _) hB

/-- A quantitative true-quotient square-mass budget. M is produced by
actual compact transporter overlap and B by the actual seed compact norm;
neither is an assumed automorphic norm bound. Sharper seed-L2 unfolding
budgets can be composed independently with the same output object. -/
theorem compactPoincare_square_mass_bound (N : ℕ) [NeZero N] (f : UpperHalfPlane → ℂ)
    (hf : Continuous f) {K : Set UpperHalfPlane} (hK : IsCompact K)
    (hsupp : Function.support f ⊆ K) :
    ∃ M : ℕ, 0 < M ∧ ∃ B : ℝ, 0 ≤ B ∧ (∀ z ∈ K, ‖f z‖ ≤ B) ∧
      (∫ u, ‖complexPoincare N f u‖ ^ 2 ∂carrierPushforward N) ≤
        ((M : ℝ) * B) ^ 2 * (carrierPushforward N univ).toReal := by
  letI : IsFiniteMeasure (carrierPushforward N) := ⟨carrierPushforward_finite N⟩
  obtain ⟨M, hM, B, hB, hseed, hbound⟩ :=
    compactSeedTrace_uniform_overlap_bound N f hf hK hsupp
  refine ⟨M, hM, B, hB, hseed, ?_⟩
  have hquotient : ∀ u, ‖complexPoincare N f u‖ ≤ (M : ℝ) * B := by
    intro u
    by_cases hu : u ∈ range (reducedProjection N)
    · obtain ⟨z, rfl⟩ := hu
      rw [complexPoincare_projection]
      exact hbound z
    · rw [complexPoincare_off_section N f hu, norm_zero]
      exact mul_nonneg (Nat.cast_nonneg _) hB
  have hlp := compactPoincare_memLp_two N f hf hK hsupp
  have hint : Integrable (fun u => ‖complexPoincare N f u‖ ^ 2) (carrierPushforward N) :=
    (memLp_two_iff_integrable_sq_norm hlp.aestronglyMeasurable).mp hlp
  have hconst : Integrable (fun _ : Gamma0OrbitSpace N => ((M : ℝ) * B) ^ 2)
      (carrierPushforward N) := integrable_const _
  calc
    _ ≤ ∫ _u, ((M : ℝ) * B) ^ 2 ∂carrierPushforward N := by
      apply integral_mono_ae hint hconst
      apply Filter.Eventually.of_forall
      intro u
      exact pow_le_pow_left₀ (norm_nonneg _) (hquotient u) 2
    _ = _ := by simp only [integral_const, smul_eq_mul, Measure.real, mul_comm]

/-- Actual effective-Gamma0 Poincare periodization of the genuine C0
compact Laplacian seed, not a relabeled whole-plane operator. -/
def quotientTensorLaplacianPoincare (N : ℕ) [NeZero N] {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) : Gamma0OrbitSpace N → ℂ :=
  complexPoincare N (finiteCoreLaplacian s T)

theorem quotientTensorLaplacianPoincare_memLp_two (N : ℕ) [NeZero N] {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) :
    MemLp (quotientTensorLaplacianPoincare N s T) 2 (carrierPushforward N) :=
  compactPoincare_memLp_two N (finiteCoreLaplacian s T)
    (finiteCoreLaplacian_continuous s T) (finiteCompactTensorSupportK_isCompact s T)
    (finiteCoreLaplacian_support_subset s T)

def quotientTensorLaplacianPoincareL2 (N : ℕ) [NeZero N] {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) : Lp ℂ 2 (carrierPushforward N) :=
  (quotientTensorLaplacianPoincare_memLp_two N s T).toLp
    (quotientTensorLaplacianPoincare N s T)

theorem quotientTensorLaplacianPoincare_projection (N : ℕ) [NeZero N] {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) (z : reducedCarrier N) :
    quotientTensorLaplacianPoincare N s T (reducedProjection N z) =
      ∑' q : effectiveGamma0 N, finiteCoreLaplacian s T (effectiveMatrixAction N q z) :=
  complexPoincare_projection N (finiteCoreLaplacian s T) z

end
end ImbalancedChen.Part3.Gamma0CompactSeedQuotientL2Budget20261025a
