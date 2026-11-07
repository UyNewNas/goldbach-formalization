import ImbalancedChen.Part3Gamma0EffectiveFiniteUnfolding
import ImbalancedChen.Part3MaassFiniteCoreL2Graph
import Mathlib.Analysis.Complex.UpperHalfPlane.ProperAction
import Mathlib.Topology.Instances.Int

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

The actual integral Gamma0 action is proper: its inclusion into SL(2,R)
is a closed embedding, and pinned Mathlib proves the real action proper.
Compact-compact collision sets are consequently finite in the discrete
integral group; their images in the genuine effective quotient are finite.

For the existing literal finite CompactTensor seed, explicit positive-height
support rectangles are compact in H. This gives a locally finite actual
effective-Gamma0 Poincare sum, equal to one finite sum throughout a
neighborhood of every point. Continuity follows from this proved local
identity. No local-finiteness assumption, integral unfolding, automorphic
operator, spectral theorem, or normalization is supplied as an input.
-/

namespace ImbalancedChen.Part3.Gamma0CompactTensorPoincareLocalFinite20261025a

noncomputable section

open Set MeasureTheory Filter Topology
open scoped UpperHalfPlane Pointwise
open ImbalancedChen.Part3.Gamma0EffectiveActionKernel20261024z
open ImbalancedChen.Part3.Gamma0EffectiveFiniteUnfolding20261025a
open ImbalancedChen.Part3.CanonicalTensorHyperbolicLaplacianForm20261024z
open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz
open ImbalancedChen.Part3.MaassFiniteCoreL2Graph20261025a

/-- Properness is pulled back through the actual closed integral matrix
inclusion. This is not a supplied proper-action hypothesis. -/
theorem gamma0_properSMul (N : ℕ) :
    ProperSMul (CongruenceSubgroup.Gamma0 N) UpperHalfPlane := by
  have hmap : IsClosedEmbedding
      (SpecialLinearGroup.map (Int.castRingHom ℝ) : SL(2, ℤ) → SL(2, ℝ)) :=
    Int.isClosedEmbedding_coe_real.specialLinearGroup_map
  letI : ProperSMul SL(2, ℤ) UpperHalfPlane :=
    properSMul_of_isClosedEmbedding (SpecialLinearGroup.map (Int.castRingHom ℝ))
      hmap (fun _ _ => rfl)
  exact properSMul_of_isClosedEmbedding (CongruenceSubgroup.Gamma0 N).subtype
    (isClosed_discrete _).isClosedEmbedding_subtypeVal (fun _ _ => rfl)

/-- Only finitely many actual integral Gamma0 matrices move one compact
set to intersect another; the central signs are still present here. -/
theorem finite_gamma0_compact_hits (N : ℕ) {K L : Set UpperHalfPlane}
    (hK : IsCompact K) (hL : IsCompact L) :
    {γ : CongruenceSubgroup.Gamma0 N | (γ • K ∩ L).Nonempty}.Finite := by
  letI := gamma0_properSMul N
  exact isCompact_iff_finite.mp
    (ProperSMul.isCompact_setOfPred_inter_nonempty hK hL)

/-- Finiteness passes to the true effective quotient, which identifies
the full scalar action kernel {+I,-I}. -/
theorem finite_effective_compact_hits (N : ℕ) {K L : Set UpperHalfPlane}
    (hK : IsCompact K) (hL : IsCompact L) :
    {q : effectiveGamma0 N | (effectiveMatrixAction N q '' K ∩ L).Nonempty}.Finite := by
  have hfinite := finite_gamma0_compact_hits N hK hL
  apply (hfinite.image
    (fun γ : CongruenceSubgroup.Gamma0 N =>
      (QuotientGroup.mk γ : effectiveGamma0 N))).subset
  intro q hq
  refine ⟨effectiveRepresentative N q, ?_, effectiveRepresentative_class N q⟩
  exact hq

/-- An explicit compact support rectangle for the existing pure tensor.
Vertical positivity is used to keep its compact image inside H. -/
def compactTensorSupportK (T : CompactTensor) : Set UpperHalfPlane :=
  {z | z.re ∈ tsupport T.horizontal ∧ z.im ∈ tsupport T.vertical}

theorem compactTensorSupportK_isCompact (T : CompactTensor) :
    IsCompact (compactTensorSupportK T) := by
  apply UpperHalfPlane.isEmbedding_coe.isCompact_iff.mpr
  have heq : ((↑) : UpperHalfPlane → ℂ) '' compactTensorSupportK T =
      (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ)) ''
        (tsupport T.horizontal ×ˢ tsupport T.vertical) := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨(z.re, z.im), hz, ?_⟩
      ext <;> rfl
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨⟨p.1, p.2⟩, T.vertical_positive hp.2⟩, hp, rfl⟩
  rw [heq]
  exact (T.horizontal_compact.prod T.vertical_compact).image (by fun_prop)

/-- The literal finite tensor seed has a finite union of these compact
rectangles as an explicit support container. -/
def finiteCompactTensorSupportK {ι : Type*} (s : Finset ι) (T : ι → CompactTensor) :
    Set UpperHalfPlane :=
  ⋃ i : {i // i ∈ s}, compactTensorSupportK (T i)

theorem finiteCompactTensorSupportK_isCompact {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) :
    IsCompact (finiteCompactTensorSupportK s T) :=
  isCompact_iUnion (fun i => compactTensorSupportK_isCompact (T i))

theorem finiteCoreFunction_support_subset {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) :
    Function.support (finiteCoreFunction s T) ⊆ finiteCompactTensorSupportK s T := by
  intro z hz
  by_contra hnot
  apply hz
  change ∑ i ∈ s, tensorFunctionH (T i).horizontal (T i).vertical z = 0
  apply Finset.sum_eq_zero
  intro i hi
  have hKi : z ∉ compactTensorSupportK (T i) := by
    intro hmem
    exact hnot (mem_iUnion.mpr ⟨⟨i, hi⟩, hmem⟩)
  rw [tensorFunctionH_eq]
  by_cases hh : z.re ∈ tsupport (T i).horizontal
  · have hv : z.im ∉ tsupport (T i).vertical := fun h => hKi ⟨hh, h⟩
    rw [image_eq_zero_of_notMem_tsupport hv, mul_zero]
  · rw [image_eq_zero_of_notMem_tsupport hh, zero_mul]

/-- A point has a neighborhood on which only finitely many actual
effective translates of any compactly supported seed can be nonzero. -/
theorem compact_seed_locally_finite (N : ℕ) (f : UpperHalfPlane → ℂ)
    {K : Set UpperHalfPlane} (hK : IsCompact K) (hsupp : Function.support f ⊆ K)
    (z : UpperHalfPlane) :
    ∃ U ∈ 𝓝 z, ∃ S : Finset (effectiveGamma0 N),
      ∀ w ∈ U, ∀ q ∉ S, f (effectiveMatrixAction N q w) = 0 := by
  classical
  obtain ⟨U, hUc, hUn⟩ := exists_compact_mem_nhds z
  have hfinite := finite_effective_compact_hits N hUc hK
  refine ⟨U, hUn, hfinite.toFinset, ?_⟩
  intro w hw q hq
  by_contra hnonzero
  apply hq
  apply hfinite.mem_toFinset.mpr
  exact ⟨effectiveMatrixAction N q w, ⟨w, hw, rfl⟩, hsupp hnonzero⟩

/-- The actual finite-tensor seed Poincare functional, indexed once per
class of the full Gamma0 action kernel. -/
def finiteCompactTensorPoincare (N : ℕ) {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) (z : UpperHalfPlane) : ℂ :=
  ∑' q : effectiveGamma0 N, finiteCoreFunction s T (effectiveMatrixAction N q z)

/-- The Poincare functional is literally a single finite sum throughout
a neighborhood, with no convergence or local-finiteness hypothesis. -/
theorem finiteCompactTensorPoincare_locally_eq_finsetSum (N : ℕ) {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) (z : UpperHalfPlane) :
    ∃ U ∈ 𝓝 z, ∃ S : Finset (effectiveGamma0 N),
      ∀ w ∈ U, finiteCompactTensorPoincare N s T w =
        ∑ q ∈ S, finiteCoreFunction s T (effectiveMatrixAction N q w) := by
  obtain ⟨U, hU, S, hS⟩ := compact_seed_locally_finite N (finiteCoreFunction s T)
    (finiteCompactTensorSupportK_isCompact s T) (finiteCoreFunction_support_subset s T) z
  refine ⟨U, hU, S, ?_⟩
  intro w hw
  exact tsum_eq_sum (fun q hq => hS w hw q hq)

/-- The local finite formula makes this actual complex Poincare seed sum
continuous. No integral-unfolding statement is used. -/
theorem finiteCompactTensorPoincare_continuous (N : ℕ) {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) :
    Continuous (finiteCompactTensorPoincare N s T) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  obtain ⟨U, hU, S, hS⟩ := finiteCompactTensorPoincare_locally_eq_finsetSum N s T z
  have hcont : Continuous (fun w : UpperHalfPlane =>
      ∑ q ∈ S, finiteCoreFunction s T (effectiveMatrixAction N q w)) := by
    apply continuous_finsetSum S
    intro q _
    apply (continuous_finiteCoreFunction s T).comp
    change Continuous (fun w : UpperHalfPlane =>
      (SpecialLinearGroup.mapGL ℝ (effectiveRepresentative N q : SL(2, ℤ))) • w)
    exact continuous_const_smul _
  apply hcont.continuousAt.congr_of_eventuallyEq
  exact Filter.eventually_of_mem hU hS

end
end ImbalancedChen.Part3.Gamma0CompactTensorPoincareLocalFinite20261025a
