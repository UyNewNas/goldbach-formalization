import Mathlib.Topology.Compactness.Compact

/-!
# Compact sets turn local common thresholds into one global threshold

The hypothesis supplies an entire parameter neighborhood with one threshold
at each center. Pointwise eventual statements alone do not meet it. A finite
neighborhood subcover and the maximum of its thresholds prove the result.
-/

namespace ImbalancedChen

open Filter Topology Set

theorem exists_uniform_threshold_on_compact_of_local
    {X : Type*} [TopologicalSpace X] (S : Set X) (hS : IsCompact S)
    (P : ℕ → X → Prop)
    (hlocal : ∀ x ∈ S, ∃ n : ℕ, ∀ᶠ y in 𝓝[S] x, ∀ N : ℕ, n ≤ N → P N y) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → ∀ x ∈ S, P N x := by
  classical
  choose n hn using fun x : S => hlocal x.val x.property
  let U := fun x : S => {y : X | ∀ N : ℕ, n x ≤ N → P N y}
  obtain ⟨t, ht⟩ := hS.elim_nhdsWithin_subcover'
    (fun x hx => U ⟨x, hx⟩) (fun x hx => hn ⟨x, hx⟩)
  refine ⟨max 2 (t.sup n), le_max_left _ _, ?_⟩
  intro N hN x hx
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht hx)
  exact hxy N ((Finset.le_sup (f := n) hy).trans ((le_max_right _ _).trans hN))

/-- Ambient neighborhoods can be restricted before applying the compact
subcover. Boundary points of the parameter set remain included. -/
theorem exists_uniform_threshold_on_compact_of_local_nhds
    {X : Type*} [TopologicalSpace X] (S : Set X) (hS : IsCompact S)
    (P : ℕ → X → Prop)
    (hlocal : ∀ x ∈ S, ∃ n : ℕ, ∀ᶠ y in 𝓝 x, ∀ N : ℕ, n ≤ N → P N y) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → ∀ x ∈ S, P N x := by
  apply exists_uniform_threshold_on_compact_of_local S hS P
  intro x hx
  obtain ⟨n, hn⟩ := hlocal x hx
  exact ⟨n, hn.filter_mono nhdsWithin_le_nhds⟩

end ImbalancedChen
