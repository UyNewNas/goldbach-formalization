import ImbalancedChen.Part3ActualResolventCyclicL2Representation
import Mathlib.Data.Set.Pairwise.Lattice
import Mathlib.Order.Zorn
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

Reducing cyclic subspaces for the actual completed-energy weak resolvent.
The cyclicSubspace is exactly the closed continuous-CFC orbit used by the
actual scalar-measure L2 representation. Both it and its orthogonal
complement are invariant under the actual resolvent. More strongly, both
are invariant under every member of its genuine complex continuous CFC.

Zorn's lemma supplies a maximal family of nonzero vectors with mutually
orthogonal actual cyclic subspaces. Any vector orthogonal to their span
generates an additional orthogonal cyclic subspace, so maximality proves
the closed span is the whole ACTUAL HyperbolicL2. No totality, invariance,
decomposition, or spectral-measure premise is supplied.
-/

namespace ImbalancedChen.Part3.ActualResolventCyclicReduction20261025a

noncomputable section

open Set MeasureTheory
open ImbalancedChen.Part3.MaassFiniteCoreL2Graph20261025a
open ImbalancedChen.Part3.ActualCompletedEnergyResolvent20261025a
open ImbalancedChen.Part3.ActualResolventScalarMeasure20261025a
open ImbalancedChen.Part3.ActualResolventContinuousCyclic20261025a
open ImbalancedChen.Part3.ActualResolventCyclicL2Representation20261025a

theorem self_mem_cyclicSubspace (f : HyperbolicL2) : f ∈ cyclicSubspace f := by
  have h := continuousCyclicMap_mem_cyclicSubspace f 1
  simpa only [continuousCyclicMap_apply, map_one, one_apply_eq_self] using h

/-- Multiplication in the actual CFC preserves the actual closed orbit. -/
theorem complexCFC_mem_cyclicSubspace (f : HyperbolicL2)
    (φ : C(ResolventSpectrum, ℂ)) {u : HyperbolicL2}
    (hu : u ∈ cyclicSubspace f) :
    (complexResolventCFC φ) u ∈ cyclicSubspace f := by
  let A := complexResolventCFC φ
  have hrange : LinearMap.range (continuousCyclicMap f) ≤
      (cyclicSubspace f).comap A.toLinearMap := by
    rintro v ⟨ψ, rfl⟩
    change (complexResolventCFC φ) (continuousCyclicMap f ψ) ∈ cyclicSubspace f
    have h := continuousCyclicMap_mem_cyclicSubspace f (φ * ψ)
    simpa only [continuousCyclicMap_apply, map_mul, mul_apply_eq_comp] using h
  have hclosed : IsClosed
      (((cyclicSubspace f).comap A.toLinearMap : Submodule ℂ HyperbolicL2) :
        Set HyperbolicL2) :=
    (isClosed_cyclicSubspace f).preimage A.continuous
  exact (LinearMap.range (continuousCyclicMap f)).topologicalClosure_minimal
    hrange hclosed hu

/-- Invariance under the genuine actual resolvent, from the coordinate
identity on the dense cyclic orbit and continuity. -/
theorem actualWeakResolvent_mem_cyclicSubspace (f : HyperbolicL2)
    {u : HyperbolicL2} (hu : u ∈ cyclicSubspace f) :
    actualWeakResolvent u ∈ cyclicSubspace f := by
  have hrange : LinearMap.range (continuousCyclicMap f) ≤
      (cyclicSubspace f).comap actualWeakResolvent.toLinearMap := by
    rintro v ⟨φ, rfl⟩
    change actualWeakResolvent (continuousCyclicMap f φ) ∈ cyclicSubspace f
    rw [← continuousCyclicMap_coordinate]
    exact continuousCyclicMap_mem_cyclicSubspace f _
  exact (LinearMap.range (continuousCyclicMap f)).topologicalClosure_minimal
    hrange ((isClosed_cyclicSubspace f).preimage actualWeakResolvent.continuous) hu

/-- The orthogonal complement is invariant because the actual operator is
self-adjoint, a theorem of its completed-energy construction. -/
theorem actualWeakResolvent_mem_cyclicSubspace_orthogonal (f : HyperbolicL2)
    {u : HyperbolicL2} (hu : u ∈ (cyclicSubspace f)ᗮ) :
    actualWeakResolvent u ∈ (cyclicSubspace f)ᗮ := by
  intro v hv
  rw [← actualWeakResolvent.adjoint_inner_left u v,
    actualWeakResolvent_selfAdjoint.adjoint_eq]
  exact hu _ (actualWeakResolvent_mem_cyclicSubspace f hv)

/-- The full star-closed CFC also preserves the orthogonal complement. -/
theorem complexCFC_mem_cyclicSubspace_orthogonal (f : HyperbolicL2)
    (φ : C(ResolventSpectrum, ℂ)) {u : HyperbolicL2}
    (hu : u ∈ (cyclicSubspace f)ᗮ) :
    (complexResolventCFC φ) u ∈ (cyclicSubspace f)ᗮ := by
  intro v hv
  rw [← (complexResolventCFC φ).adjoint_inner_left u v]
  have hstar : (complexResolventCFC φ).adjoint = complexResolventCFC (star φ) := by
    rw [map_star, ContinuousLinearMap.star_eq_adjoint]
  rw [hstar]
  exact hu _ (complexCFC_mem_cyclicSubspace f (star φ) hv)

/-- A vector orthogonal to a cyclic subspace generates an entire cyclic
subspace orthogonal to it, including the closure. -/
theorem cyclicSubspace_le_orthogonal_of_mem {f g : HyperbolicL2}
    (hg : g ∈ (cyclicSubspace f)ᗮ) :
    cyclicSubspace g ≤ (cyclicSubspace f)ᗮ := by
  apply (LinearMap.range (continuousCyclicMap g)).topologicalClosure_minimal
  · rintro u ⟨φ, rfl⟩
    exact complexCFC_mem_cyclicSubspace_orthogonal f φ hg
  · exact (cyclicSubspace f).isClosed_orthogonal

/-- Nonzero seeds with genuinely orthogonal actual cyclic spaces. -/
def OrthogonalCyclicSeeds (s : Set HyperbolicL2) : Prop :=
  s.Pairwise (fun f g => cyclicSubspace f ⟂ cyclicSubspace g) ∧
    ∀ f ∈ s, f ≠ 0

theorem orthogonalCyclicSeeds_empty : OrthogonalCyclicSeeds ∅ := by
  constructor
  · exact Set.pairwise_empty _
  · simp

theorem orthogonalCyclicSeeds_sUnion {c : Set (Set HyperbolicL2)}
    (hc : IsChain (· ⊆ ·) c) (h : ∀ s ∈ c, OrthogonalCyclicSeeds s) :
    OrthogonalCyclicSeeds (⋃₀ c) := by
  constructor
  · exact (Set.pairwise_sUnion hc.directedOn).mpr (fun s hs => (h s hs).1)
  · intro f hf
    obtain ⟨s, hs, hfs⟩ := Set.mem_sUnion.mp hf
    exact (h s hs).2 f hfs

/-- A maximal family is constructed by actual chain unions. -/
theorem exists_maximal_orthogonalCyclicSeeds :
    ∃ s : Set HyperbolicL2, OrthogonalCyclicSeeds s ∧
      ∀ t, s ⊆ t → OrthogonalCyclicSeeds t → t = s := by
  have h := zorn_subset_nonempty {s : Set HyperbolicL2 | OrthogonalCyclicSeeds s}
    (fun c hc hchain _ =>
      ⟨⋃₀ c, orthogonalCyclicSeeds_sUnion hchain (fun s hs => hc hs),
        fun _ hs => Set.subset_sUnion_of_mem hs⟩)
    ∅ orthogonalCyclicSeeds_empty
  obtain ⟨s, _, hs⟩ := h
  exact ⟨s, hs.1, fun t hst ht => hs.eq_of_ge ht hst⟩

def cyclicFamilySpan (s : Set HyperbolicL2) : Submodule ℂ HyperbolicL2 :=
  ⨆ f : s, cyclicSubspace (f : HyperbolicL2)

theorem cyclicSubspace_le_familySpan {s : Set HyperbolicL2}
    {f : HyperbolicL2} (hf : f ∈ s) : cyclicSubspace f ≤ cyclicFamilySpan s :=
  le_iSup (fun g : s => cyclicSubspace (g : HyperbolicL2)) ⟨f, hf⟩

/-- Maximality forces totality: an orthogonal leftover vector would add a
nonzero actual cyclic space. The totality statement is a conclusion. -/
theorem maximal_cyclicFamilySpan_dense {s : Set HyperbolicL2}
    (hs : OrthogonalCyclicSeeds s)
    (hmax : ∀ t, s ⊆ t → OrthogonalCyclicSeeds t → t = s) :
    (cyclicFamilySpan s).topologicalClosure = ⊤ := by
  apply (cyclicFamilySpan s).topologicalClosure_eq_top_iff.mpr
  apply Submodule.eq_bot_iff.mpr
  intro g hg
  by_contra hne
  have hnot : g ∉ s := by
    intro hgs
    have hgin : g ∈ cyclicFamilySpan s :=
      cyclicSubspace_le_familySpan hgs (self_mem_cyclicSubspace g)
    exact hne (inner_self_eq_zero.mp (hg g hgin))
  have hins : OrthogonalCyclicSeeds (insert g s) := by
    constructor
    · apply hs.1.insert_of_notMem hnot
      intro f hf
      have hgf : g ∈ (cyclicSubspace f)ᗮ :=
        Submodule.orthogonal_le (cyclicSubspace_le_familySpan hf) hg
      have hspaces : cyclicSubspace g ⟂ cyclicSubspace f :=
        cyclicSubspace_le_orthogonal_of_mem hgf
      exact ⟨hspaces, hspaces.symm⟩
    · intro f hf
      rcases Set.mem_insert_iff.mp hf with rfl | hf
      · exact hne
      · exact hs.2 f hf
  have heq : insert g s = s := hmax _ (Set.subset_insert g s) hins
  exact hnot (heq ▸ Set.mem_insert g s)

/-- The actual Hilbert space admits a maximal orthogonal TOTAL family of
its genuine reducing cyclic subspaces. No spectral expansion is assumed. -/
theorem exists_maximal_total_actual_cyclic_family :
    ∃ s : Set HyperbolicL2,
      OrthogonalCyclicSeeds s ∧
      (∀ t, s ⊆ t → OrthogonalCyclicSeeds t → t = s) ∧
      (cyclicFamilySpan s).topologicalClosure = ⊤ := by
  obtain ⟨s, hs, hmax⟩ := exists_maximal_orthogonalCyclicSeeds
  exact ⟨s, hs, hmax, maximal_cyclicFamilySpan_dense hs hmax⟩

/-- A fixed maximal family for subsequent Hilbert-sum construction. -/
def actualCyclicSeeds : Set HyperbolicL2 :=
  Classical.choose exists_maximal_total_actual_cyclic_family

theorem actualCyclicSeeds_orthogonal : OrthogonalCyclicSeeds actualCyclicSeeds :=
  (Classical.choose_spec exists_maximal_total_actual_cyclic_family).1

theorem actualCyclicSeeds_total :
    (cyclicFamilySpan actualCyclicSeeds).topologicalClosure = ⊤ :=
  (Classical.choose_spec exists_maximal_total_actual_cyclic_family).2.2

end
end ImbalancedChen.Part3.ActualResolventCyclicReduction20261025a
