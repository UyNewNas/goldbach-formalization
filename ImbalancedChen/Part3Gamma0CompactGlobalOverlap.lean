import ImbalancedChen.Part3Gamma0CompactTensorPoincareC2Core
import Mathlib.Data.Set.Card

/-!
# A global uniform compact-orbit overlap bound for actual Gamma0

SOURCE_WRITTEN / UNCOMPILED / NOT_ROOT_ACCEPTED.

The compact-compact transporter has already been proved finite from actual
integral-matrix properness. If one orbit point hits K, fix one hitting label
r. Every other hitting label q maps injectively to q*r^-1 in the SAME
compact transporter of K with itself. Its finite cardinal therefore bounds
the number of hits at EVERY point of H, with no local compact neighborhood
or point-dependent bound. We prove this for the actual integral Gamma0 and
for the exact effective quotient used by the existing Poincare sum.

No global-overlap, L2, spectral or automorphic-operator conclusion is a
premise. The effective quotient is by the already identified full scalar
action kernel, so +I/-I are not counted twice in the Poincare corollary.
-/

namespace ImbalancedChen.Part3.Gamma0CompactGlobalOverlap20261025a
noncomputable section
open Set
open scoped UpperHalfPlane Pointwise
open ImbalancedChen.Part3.Gamma0EffectiveActionKernel20261024z
open ImbalancedChen.Part3.Gamma0EffectiveFiniteUnfolding20261025a
open ImbalancedChen.Part3.Gamma0CompactTensorPoincareLocalFinite20261025a
open ImbalancedChen.Part3.Gamma0CompactTensorPoincareC2Core20261025a
open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz

def gamma0CompactHitSet (N : ℕ) (K : Set UpperHalfPlane) (z : UpperHalfPlane) :
    Set (CongruenceSubgroup.Gamma0 N) := {γ | γ • z ∈ K}

def gamma0CompactTransporter (N : ℕ) (K : Set UpperHalfPlane) :
    Set (CongruenceSubgroup.Gamma0 N) := {γ | (γ • K ∩ K).Nonempty}

/-- The full actual group also has a finite uniform overlap bound; its
finite scalar kernel is retained in this first statement. -/
theorem gamma0_compact_hits_finite_and_card_le (N : ℕ)
    {K : Set UpperHalfPlane} (hK : IsCompact K) (z : UpperHalfPlane) :
    (gamma0CompactHitSet N K z).Finite ∧
      (gamma0CompactHitSet N K z).ncard ≤ (gamma0CompactTransporter N K).ncard := by
  have hT : (gamma0CompactTransporter N K).Finite := finite_gamma0_compact_hits N hK hK
  by_cases hhit : (gamma0CompactHitSet N K z).Nonempty
  · obtain ⟨r, hr⟩ := hhit
    have hm : MapsTo (fun q : CongruenceSubgroup.Gamma0 N => q * r⁻¹)
        (gamma0CompactHitSet N K z) (gamma0CompactTransporter N K) := by
      intro q hq
      refine ⟨q • z, ?_, hq⟩
      exact ⟨r • z, hr, by simp only [mul_smul, inv_smul_smul]⟩
    have hinj : InjOn (fun q : CongruenceSubgroup.Gamma0 N => q * r⁻¹)
        (gamma0CompactHitSet N K z) := by
      intro q hq p hp heq
      exact mul_right_cancel heq
    exact ⟨Set.Finite.of_injOn hm hinj hT,
      Set.ncard_le_ncard_of_injOn _ hm hinj hT⟩
  · have he : gamma0CompactHitSet N K z = ∅ := Set.not_nonempty_iff_eq_empty.mp hhit
    simp only [he, finite_empty, ncard_empty, Nat.zero_le, and_self]

def compactHitSet (N : ℕ) (K : Set UpperHalfPlane) (z : UpperHalfPlane) :
    Set (effectiveGamma0 N) := {q | effectiveMatrixAction N q z ∈ K}

def compactTransporter (N : ℕ) (K : Set UpperHalfPlane) : Set (effectiveGamma0 N) :=
  {q | (effectiveMatrixAction N q '' K ∩ K).Nonempty}

/-- Multiplicativity is the proved actual representative-action theorem,
not a new action field or an assumption about chosen representatives. -/
theorem effectiveMatrixAction_relative (N : ℕ) (q r : effectiveGamma0 N)
    (z : UpperHalfPlane) :
    effectiveMatrixAction N (q * r⁻¹) (effectiveMatrixAction N r z) =
      effectiveMatrixAction N q z := by
  calc
    _ = effectiveMatrixAction N ((q * r⁻¹) * r) z :=
      (effectiveMatrixAction_mul N (q * r⁻¹) r z).symm
    _ = effectiveMatrixAction N q z := by simp only [mul_assoc, inv_mul_cancel, mul_one]

/-- Global cardinal bound in the actual effective Gamma0 index group.
The right side depends only on N and K, never on z. -/
theorem compact_hits_finite_and_card_le (N : ℕ)
    {K : Set UpperHalfPlane} (hK : IsCompact K) (z : UpperHalfPlane) :
    (compactHitSet N K z).Finite ∧
      (compactHitSet N K z).ncard ≤ (compactTransporter N K).ncard := by
  have hT : (compactTransporter N K).Finite := finite_effective_compact_hits N hK hK
  by_cases hhit : (compactHitSet N K z).Nonempty
  · obtain ⟨r, hr⟩ := hhit
    have hm : MapsTo (fun q : effectiveGamma0 N => q * r⁻¹)
        (compactHitSet N K z) (compactTransporter N K) := by
      intro q hq
      refine ⟨effectiveMatrixAction N q z, ?_, hq⟩
      exact ⟨effectiveMatrixAction N r z, hr, effectiveMatrixAction_relative N q r z⟩
    have hinj : InjOn (fun q : effectiveGamma0 N => q * r⁻¹) (compactHitSet N K z) := by
      intro q hq p hp heq
      exact mul_right_cancel heq
    exact ⟨Set.Finite.of_injOn hm hinj hT,
      Set.ncard_le_ncard_of_injOn _ hm hinj hT⟩
  · have he : compactHitSet N K z = ∅ := Set.not_nonempty_iff_eq_empty.mp hhit
    simp only [he, finite_empty, ncard_empty, Nat.zero_le, and_self]

/-- An explicit positive bound, also valid for the empty compact support. -/
def compactOverlapBound (N : ℕ) (K : Set UpperHalfPlane) : ℕ :=
  (compactTransporter N K).ncard + 1

theorem compactOverlapBound_pos (N : ℕ) (K : Set UpperHalfPlane) :
    0 < compactOverlapBound N K := Nat.zero_lt_succ _

theorem exists_uniform_finite_orbit_hits (N : ℕ)
    {K : Set UpperHalfPlane} (hK : IsCompact K) :
    ∃ M : ℕ, 0 < M ∧ ∀ z : UpperHalfPlane,
      (compactHitSet N K z).Finite ∧ (compactHitSet N K z).ncard ≤ M := by
  refine ⟨compactOverlapBound N K, compactOverlapBound_pos N K, ?_⟩
  intro z
  have h := compact_hits_finite_and_card_le N hK z
  exact ⟨h.1, h.2.trans (Nat.le_succ _)⟩

/-- Global finite support for every compactly supported complex seed,
with the SAME cardinal bound at all points of the upper half-plane. -/
theorem compact_seed_uniform_finite_support (N : ℕ) (f : UpperHalfPlane → ℂ)
    {K : Set UpperHalfPlane} (hK : IsCompact K) (hsupp : Function.support f ⊆ K) :
    ∃ M : ℕ, 0 < M ∧ ∀ z : UpperHalfPlane, ∃ S : Finset (effectiveGamma0 N),
      S.card ≤ M ∧ ∀ q ∉ S, f (effectiveMatrixAction N q z) = 0 := by
  obtain ⟨M, hM, hbound⟩ := exists_uniform_finite_orbit_hits N hK
  refine ⟨M, hM, ?_⟩
  intro z
  have hfinite := (hbound z).1
  refine ⟨hfinite.toFinset, ?_, ?_⟩
  · rw [← Set.ncard_eq_toFinset_card (compactHitSet N K z) hfinite]
    exact (hbound z).2
  · intro q hq
    by_contra hnonzero
    exact hq (hfinite.mem_toFinset.mpr (hsupp hnonzero))

theorem compact_seed_translate_support_finite_and_card_le
    (N : ℕ) (f : UpperHalfPlane → ℂ) {K : Set UpperHalfPlane}
    (hK : IsCompact K) (hsupp : Function.support f ⊆ K) (z : UpperHalfPlane) :
    (Function.support (fun q : effectiveGamma0 N => f (effectiveMatrixAction N q z))).Finite ∧
      (Function.support (fun q : effectiveGamma0 N => f (effectiveMatrixAction N q z))).ncard ≤
        compactOverlapBound N K := by
  have hh := compact_hits_finite_and_card_le N hK z
  have hsub : Function.support (fun q : effectiveGamma0 N => f (effectiveMatrixAction N q z)) ⊆
      compactHitSet N K z := fun q hq => hsupp hq
  exact ⟨hh.1.subset hsub,
    (Set.ncard_le_ncard hsub hh.1).trans (hh.2.trans (Nat.le_succ _))⟩

/-- The actual finite-CompactTensor Poincare seed receives a genuinely
GLOBAL overlap constant. No local-finiteness hypothesis is repeated. -/
theorem finiteCompactTensor_uniform_finite_support (N : ℕ) {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) :
    ∃ M : ℕ, 0 < M ∧ ∀ z : UpperHalfPlane, ∃ S : Finset (effectiveGamma0 N),
      S.card ≤ M ∧ ∀ q ∉ S, finiteCoreFunction s T (effectiveMatrixAction N q z) = 0 :=
  compact_seed_uniform_finite_support N (finiteCoreFunction s T)
    (finiteCompactTensorSupportK_isCompact s T) (finiteCoreFunction_support_subset s T)

end
end ImbalancedChen.Part3.Gamma0CompactGlobalOverlap20261025a
