import ImbalancedChen.Part3GenericResolventCyclicIntertwining
import Mathlib.Data.Set.Pairwise.Lattice
import Mathlib.Order.Zorn
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Lp.lpHolder

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

A generic global scalar spectral assembly for ANY bounded self-adjoint
operator on ANY complex Hilbert space. All reducing, maximality, totality,
Hilbert sum and diagonalization arguments are proved with variable H,R.
There are no concrete whole-plane imports or fixed-space aliases, no
countability assumption and no totality/unitary supplier. The diagonal
coordinate multiplier is bounded by norm R; positivity is not assumed.
-/

namespace ImbalancedChen.Part3.GenericResolventGlobalSpectralAssembly20261025a

noncomputable section
open Set MeasureTheory
open ImbalancedChen.Part3.GenericResolventScalarMeasure20261025a
open ImbalancedChen.Part3.GenericResolventCyclicL2Representation20261025a
open ImbalancedChen.Part3.GenericResolventCyclicIntertwining20261025a

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R)

theorem self_mem_cyclicSubspace (f : H) : f ∈ (cyclicSubspace R hSA) f := by
  have h := (continuousCyclicMap_mem_cyclicSubspace R hSA) f 1
  simpa only [(continuousCyclicMap_apply R hSA), map_one, one_apply_eq_self] using h

/-- Multiplication in the actual CFC preserves the actual closed orbit. -/
theorem complexCFC_mem_cyclicSubspace (f : H)
    (φ : C((ResolventSpectrum R), ℂ)) {u : H}
    (hu : u ∈ (cyclicSubspace R hSA) f) :
    ((complexResolventCFC R hSA) φ) u ∈ (cyclicSubspace R hSA) f := by
  let A := (complexResolventCFC R hSA) φ
  have hrange : LinearMap.range ((continuousCyclicMap R hSA) f) ≤
      ((cyclicSubspace R hSA) f).comap A.toLinearMap := by
    rintro v ⟨ψ, rfl⟩
    change ((complexResolventCFC R hSA) φ) ((continuousCyclicMap R hSA) f ψ) ∈ (cyclicSubspace R hSA) f
    have h := (continuousCyclicMap_mem_cyclicSubspace R hSA) f (φ * ψ)
    simpa only [(continuousCyclicMap_apply R hSA), map_mul, mul_apply_eq_comp] using h
  have hclosed : IsClosed
      ((((cyclicSubspace R hSA) f).comap A.toLinearMap : Submodule ℂ H) :
        Set H) :=
    ((isClosed_cyclicSubspace R hSA) f).preimage A.continuous
  exact (LinearMap.range ((continuousCyclicMap R hSA) f)).topologicalClosure_minimal
    hrange hclosed hu

/-- Invariance under the genuine actual resolvent, from the coordinate
identity on the dense cyclic orbit and continuity. -/
theorem resolvent_mem_cyclicSubspace (f : H)
    {u : H} (hu : u ∈ (cyclicSubspace R hSA) f) :
    R u ∈ (cyclicSubspace R hSA) f := by
  have hrange : LinearMap.range ((continuousCyclicMap R hSA) f) ≤
      ((cyclicSubspace R hSA) f).comap R.toLinearMap := by
    rintro v ⟨φ, rfl⟩
    change R ((continuousCyclicMap R hSA) f φ) ∈ (cyclicSubspace R hSA) f
    rw [← (continuousCyclicMap_coordinate R hSA)]
    exact (continuousCyclicMap_mem_cyclicSubspace R hSA) f _
  exact (LinearMap.range ((continuousCyclicMap R hSA) f)).topologicalClosure_minimal
    hrange (((isClosed_cyclicSubspace R hSA) f).preimage R.continuous) hu

/-- The orthogonal complement is invariant because the actual operator is
self-adjoint, exactly the specified hSA property. -/
theorem resolvent_mem_cyclicSubspace_orthogonal (f : H)
    {u : H} (hu : u ∈ ((cyclicSubspace R hSA) f)ᗮ) :
    R u ∈ ((cyclicSubspace R hSA) f)ᗮ := by
  intro v hv
  rw [← R.adjoint_inner_left u v,
    hSA.adjoint_eq]
  exact hu _ ((resolvent_mem_cyclicSubspace R hSA) f hv)

/-- The full star-closed CFC also preserves the orthogonal complement. -/
theorem complexCFC_mem_cyclicSubspace_orthogonal (f : H)
    (φ : C((ResolventSpectrum R), ℂ)) {u : H}
    (hu : u ∈ ((cyclicSubspace R hSA) f)ᗮ) :
    ((complexResolventCFC R hSA) φ) u ∈ ((cyclicSubspace R hSA) f)ᗮ := by
  intro v hv
  rw [← ((complexResolventCFC R hSA) φ).adjoint_inner_left u v]
  have hstar : ((complexResolventCFC R hSA) φ).adjoint = (complexResolventCFC R hSA) (star φ) := by
    rw [map_star, ContinuousLinearMap.star_eq_adjoint]
  rw [hstar]
  exact hu _ ((complexCFC_mem_cyclicSubspace R hSA) f (star φ) hv)

/-- A vector orthogonal to a cyclic subspace generates an entire cyclic
subspace orthogonal to it, including the closure. -/
theorem cyclicSubspace_le_orthogonal_of_mem {f g : H}
    (hg : g ∈ ((cyclicSubspace R hSA) f)ᗮ) :
    (cyclicSubspace R hSA) g ≤ ((cyclicSubspace R hSA) f)ᗮ := by
  apply (LinearMap.range ((continuousCyclicMap R hSA) g)).topologicalClosure_minimal
  · rintro u ⟨φ, rfl⟩
    exact (complexCFC_mem_cyclicSubspace_orthogonal R hSA) f φ hg
  · exact ((cyclicSubspace R hSA) f).isClosed_orthogonal

/-- Nonzero seeds with genuinely orthogonal actual cyclic spaces. -/
def OrthogonalCyclicSeeds (s : Set H) : Prop :=
  s.Pairwise (fun f g => (cyclicSubspace R hSA) f ⟂ (cyclicSubspace R hSA) g) ∧
    ∀ f ∈ s, f ≠ 0

theorem orthogonalCyclicSeeds_empty : (OrthogonalCyclicSeeds R hSA) ∅ := by
  constructor
  · exact Set.pairwise_empty _
  · simp

theorem orthogonalCyclicSeeds_sUnion {c : Set (Set H)}
    (hc : IsChain (· ⊆ ·) c) (h : ∀ s ∈ c, (OrthogonalCyclicSeeds R hSA) s) :
    (OrthogonalCyclicSeeds R hSA) (⋃₀ c) := by
  constructor
  · exact (Set.pairwise_sUnion hc.directedOn).mpr (fun s hs => (h s hs).1)
  · intro f hf
    obtain ⟨s, hs, hfs⟩ := Set.mem_sUnion.mp hf
    exact (h s hs).2 f hfs

/-- A maximal family is constructed by actual chain unions. -/
theorem exists_maximal_orthogonalCyclicSeeds :
    ∃ s : Set H, (OrthogonalCyclicSeeds R hSA) s ∧
      ∀ t, s ⊆ t → (OrthogonalCyclicSeeds R hSA) t → t = s := by
  have h := zorn_subset_nonempty {s : Set H | (OrthogonalCyclicSeeds R hSA) s}
    (fun c hc hchain _ =>
      ⟨⋃₀ c, (orthogonalCyclicSeeds_sUnion R hSA) hchain (fun s hs => hc hs),
        fun _ hs => Set.subset_sUnion_of_mem hs⟩)
    ∅ (orthogonalCyclicSeeds_empty R hSA)
  obtain ⟨s, _, hs⟩ := h
  exact ⟨s, hs.1, fun t hst ht => hs.eq_of_ge ht hst⟩

def cyclicFamilySpan (s : Set H) : Submodule ℂ H :=
  ⨆ f : s, (cyclicSubspace R hSA) (f : H)

theorem cyclicSubspace_le_familySpan {s : Set H}
    {f : H} (hf : f ∈ s) : (cyclicSubspace R hSA) f ≤ (cyclicFamilySpan R hSA) s :=
  le_iSup (fun g : s => (cyclicSubspace R hSA) (g : H)) ⟨f, hf⟩

/-- Maximality forces totality: an orthogonal leftover vector would add a
nonzero actual cyclic space. The totality statement is a conclusion. -/
theorem maximal_cyclicFamilySpan_dense {s : Set H}
    (hs : (OrthogonalCyclicSeeds R hSA) s)
    (hmax : ∀ t, s ⊆ t → (OrthogonalCyclicSeeds R hSA) t → t = s) :
    ((cyclicFamilySpan R hSA) s).topologicalClosure = ⊤ := by
  apply ((cyclicFamilySpan R hSA) s).topologicalClosure_eq_top_iff.mpr
  apply Submodule.eq_bot_iff.mpr
  intro g hg
  by_contra hne
  have hnot : g ∉ s := by
    intro hgs
    have hgin : g ∈ (cyclicFamilySpan R hSA) s :=
      (cyclicSubspace_le_familySpan R hSA) hgs ((self_mem_cyclicSubspace R hSA) g)
    exact hne (inner_self_eq_zero.mp (hg g hgin))
  have hins : (OrthogonalCyclicSeeds R hSA) (insert g s) := by
    constructor
    · apply hs.1.insert_of_notMem hnot
      intro f hf
      have hgf : g ∈ ((cyclicSubspace R hSA) f)ᗮ :=
        Submodule.orthogonal_le ((cyclicSubspace_le_familySpan R hSA) hf) hg
      have hspaces : (cyclicSubspace R hSA) g ⟂ (cyclicSubspace R hSA) f :=
        (cyclicSubspace_le_orthogonal_of_mem R hSA) hgf
      exact ⟨hspaces, hspaces.symm⟩
    · intro f hf
      rcases Set.mem_insert_iff.mp hf with rfl | hf
      · exact hne
      · exact hs.2 f hf
  have heq : insert g s = s := hmax _ (Set.subset_insert g s) hins
  exact hnot (heq ▸ Set.mem_insert g s)

/-- The actual Hilbert space admits a maximal orthogonal TOTAL family of
its genuine reducing cyclic subspaces. No spectral expansion is assumed. -/
theorem exists_maximal_total_cyclic_family :
    ∃ s : Set H,
      (OrthogonalCyclicSeeds R hSA) s ∧
      (∀ t, s ⊆ t → (OrthogonalCyclicSeeds R hSA) t → t = s) ∧
      ((cyclicFamilySpan R hSA) s).topologicalClosure = ⊤ := by
  obtain ⟨s, hs, hmax⟩ := (exists_maximal_orthogonalCyclicSeeds R hSA)
  exact ⟨s, hs, hmax, (maximal_cyclicFamilySpan_dense R hSA) hs hmax⟩

/-- A fixed maximal family for subsequent Hilbert-sum construction. -/
def spectralCyclicSeeds : Set H :=
  Classical.choose (exists_maximal_total_cyclic_family R hSA)

theorem spectralCyclicSeeds_orthogonal : (OrthogonalCyclicSeeds R hSA) (spectralCyclicSeeds R hSA) :=
  (Classical.choose_spec (exists_maximal_total_cyclic_family R hSA)).1

theorem spectralCyclicSeeds_total :
    ((cyclicFamilySpan R hSA) (spectralCyclicSeeds R hSA)).topologicalClosure = ⊤ :=
  (Classical.choose_spec (exists_maximal_total_cyclic_family R hSA)).2.2


abbrev SpectralIndex := (spectralCyclicSeeds R hSA)

local instance : DecidableEq (SpectralIndex R hSA) := Classical.decEq _

abbrev SpectralFiber (i : (SpectralIndex R hSA)) := (ScalarL2 R hSA) (i : H)

abbrev SpectralSum := lp (SpectralFiber R hSA) 2

def fiberEmbedding (i : (SpectralIndex R hSA)) :
    (SpectralFiber R hSA) i →ₗᵢ[ℂ] H := (cyclicIsometry R hSA) (i : H)

theorem fiberEmbedding_range (i : (SpectralIndex R hSA)) :
    ((fiberEmbedding R hSA) i).toLinearMap.range = (cyclicSubspace R hSA) (i : H) :=
  (cyclicIsometry_range_eq R hSA) (i : H)

/-- Pairwise orthogonality is proved from the actual Zorn family and the
exact ranges of the actual scalar-measure cyclic embeddings. -/
theorem fiberEmbedding_orthogonal :
    OrthogonalFamily ℂ (SpectralFiber R hSA) (fiberEmbedding R hSA) := by
  intro i j hij ξ η
  have hne : (i : H) ≠ (j : H) := by
    intro h
    exact hij (Subtype.ext h)
  have hspaces : (cyclicSubspace R hSA) (i : H) ⟂ (cyclicSubspace R hSA) (j : H) :=
    (spectralCyclicSeeds_orthogonal R hSA).1 i.property j.property hne
  apply hspaces.inner_eq
  · rw [← (fiberEmbedding_range R hSA) i]
    exact ⟨ξ, rfl⟩
  · rw [← (fiberEmbedding_range R hSA) j]
    exact ⟨η, rfl⟩

theorem fiberEmbedding_total :
    (⨆ i : (SpectralIndex R hSA), ((fiberEmbedding R hSA) i).toLinearMap.range).topologicalClosure =
      (⊤ : Submodule ℂ H) := by
  simp only [(fiberEmbedding_range R hSA)]
  exact (spectralCyclicSeeds_total R hSA)

/-- The actual complete Hilbert space is the Hilbert sum of its actual
scalar spectral measures; onto follows from actual totality. -/
def scalarHilbertSum :
    IsHilbertSum ℂ (SpectralFiber R hSA) (fiberEmbedding R hSA) :=
  IsHilbertSum.mk (fiberEmbedding_orthogonal R hSA)
    (by rw [(fiberEmbedding_total R hSA)])

/-- The unitary for the given Hilbert space, in the synthesis direction. -/
def spectralUnitary : (SpectralSum R hSA) ≃ₗᵢ[ℂ] H :=
  (scalarHilbertSum R hSA).linearIsometryEquiv.symm

theorem spectralUnitary_apply (ξ : (SpectralSum R hSA)) :
    (spectralUnitary R hSA) ξ = ∑' i : (SpectralIndex R hSA), (fiberEmbedding R hSA) i (ξ i) :=
  (scalarHilbertSum R hSA).linearIsometryEquiv_symm_apply ξ

theorem spectralUnitary_hasSum (ξ : (SpectralSum R hSA)) :
    HasSum (fun i : (SpectralIndex R hSA) => (fiberEmbedding R hSA) i (ξ i))
      ((spectralUnitary R hSA) ξ) :=
  (scalarHilbertSum R hSA).hasSum_linearIsometryEquiv_symm ξ

theorem spectralUnitary_norm (ξ : (SpectralSum R hSA)) :
    ‖(spectralUnitary R hSA) ξ‖ = ‖ξ‖ := (spectralUnitary R hSA).norm_map ξ

/-- Every vector of the given Hilbert space is reconstructed by its actual cyclic
scalar coordinates, including for the unrestricted index set. -/
theorem spectral_reconstruction (f : H) :
    (∑' i : (SpectralIndex R hSA),
      (fiberEmbedding R hSA) i (((spectralUnitary R hSA).symm f) i)) = f := by
  rw [← (spectralUnitary_apply R hSA), (spectralUnitary R hSA).apply_symm_apply]

theorem spectralUnitary_single (i : (SpectralIndex R hSA))
    (ξ : (SpectralFiber R hSA) i) :
    (spectralUnitary R hSA) (lp.single 2 i ξ) = (fiberEmbedding R hSA) i ξ := by
  classical
  exact (scalarHilbertSum R hSA).linearIsometryEquiv_symm_apply_single ξ


/-- Uniformly bounded actual coordinate multiplication on every actual
scalar-measure fiber. No countability restriction on the family is needed. -/
def diagonalResolvent : (SpectralSum R hSA) →L[ℂ] (SpectralSum R hSA) :=
  lp.mapCLM 2 (fun i : (SpectralIndex R hSA) => (coordinateMultiplier R hSA) (i : H))
    (norm_nonneg R) (fun i => (coordinateMultiplier_opNorm_le R hSA) (i : H))

theorem diagonalResolvent_apply (ξ : (SpectralSum R hSA)) (i : (SpectralIndex R hSA)) :
    (diagonalResolvent R hSA) ξ i = (coordinateMultiplier R hSA) (i : H) (ξ i) := rfl

theorem diagonalResolvent_opNorm_le : ‖(diagonalResolvent R hSA)‖ ≤ ‖R‖ :=
  lp.norm_mapCLM_le 2
    (fun i : (SpectralIndex R hSA) => (coordinateMultiplier R hSA) (i : H))
    (norm_nonneg R) (fun i => (coordinateMultiplier_opNorm_le R hSA) (i : H))

/-- The diagonal entries are actual multiplication by the spectral
coordinate, almost everywhere for the actual RMK scalar measures. -/
theorem diagonalResolvent_coordinate_ae (ξ : (SpectralSum R hSA))
    (i : (SpectralIndex R hSA)) :
    (diagonalResolvent R hSA) ξ i =ᵐ[(scalarMeasure R hSA) (i : H)]
      (fun t : (ResolventSpectrum R) => (t : ℂ) * (ξ i) t) :=
  (coordinateMultiplier_coe_ae R hSA) (i : H) (ξ i)

theorem fiberEmbedding_intertwine (i : (SpectralIndex R hSA))
    (ξ : (SpectralFiber R hSA) i) :
    (fiberEmbedding R hSA) i ((coordinateMultiplier R hSA) (i : H) ξ) =
      R ((fiberEmbedding R hSA) i ξ) :=
  (cyclicExtension_intertwine R hSA) (i : H) ξ

/-- Global intertwining follows from two actual convergent sums and the
proved cyclic intertwining. No summation or diagonalization supplier. -/
theorem spectralUnitary_intertwine (ξ : (SpectralSum R hSA)) :
    (spectralUnitary R hSA) ((diagonalResolvent R hSA) ξ) =
      R ((spectralUnitary R hSA) ξ) := by
  have hleft := (spectralUnitary_hasSum R hSA) ((diagonalResolvent R hSA) ξ)
  have hright := R.hasSum ((spectralUnitary_hasSum R hSA) ξ)
  have hterms :
      (fun i : (SpectralIndex R hSA) => (fiberEmbedding R hSA) i ((diagonalResolvent R hSA) ξ i)) =
        (fun i : (SpectralIndex R hSA) => R ((fiberEmbedding R hSA) i (ξ i))) := by
    funext i
    rw [(diagonalResolvent_apply R hSA)]
    exact (fiberEmbedding_intertwine R hSA) i (ξ i)
  rw [hterms] at hleft
  exact hleft.unique hright

/-- The specified operator in its whole-space scalar spectral coordinates. -/
theorem resolvent_spectral_coordinates (f : H) :
    (spectralUnitary R hSA).symm (R f) =
      (diagonalResolvent R hSA) ((spectralUnitary R hSA).symm f) := by
  apply (spectralUnitary R hSA).injective
  rw [(spectralUnitary R hSA).apply_symm_apply, (spectralUnitary_intertwine R hSA),
    (spectralUnitary R hSA).apply_symm_apply]

/-- Operator-level conjugacy for the specified arbitrary bounded self-adjoint R. -/
theorem resolvent_unitary_conjugacy :
    R =
      (spectralUnitary R hSA).toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((diagonalResolvent R hSA).comp
          (spectralUnitary R hSA).symm.toContinuousLinearEquiv.toContinuousLinearMap) := by
  ext f
  change R f =
    (spectralUnitary R hSA) ((diagonalResolvent R hSA) ((spectralUnitary R hSA).symm f))
  rw [(spectralUnitary_intertwine R hSA), (spectralUnitary R hSA).apply_symm_apply]



end
end ImbalancedChen.Part3.GenericResolventGlobalSpectralAssembly20261025a


