import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.WeakDual

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Sequential weak compactness derived from pinned sequential Banach--Alaoglu
and Frechet--Riesz, rather than supplied as a weak-limit hypothesis. -/

namespace ImbalancedChen.Part3.HilbertBoundedWeakSubsequence20261026b
noncomputable section
open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [TopologicalSpace.SeparableSpace E]

/-- Every norm bounded sequence in a separable complex Hilbert space has
a genuinely extracted weak subsequence, with its original norm bound. -/
theorem exists_bounded_weak_subsequence (u : ℕ → E) (C : ℝ)
    (hu : ∀ n, ‖u n‖ ≤ C) :
    ∃ g : E, ‖g‖ ≤ C ∧ ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ z : E, Tendsto (fun n => inner ℂ z (u (σ n))) atTop
        (𝓝 (inner ℂ z g)) := by
  let w : ℕ → WeakDual ℂ E := fun n =>
    (InnerProductSpace.toDual ℂ E (u n)).toWeakDual
  have hw (n : ℕ) : w n ∈
      WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℂ E) C := by
    simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right,
      w, StrongDual.toStrongDual_toWeakDual, LinearIsometryEquiv.norm_map] using hu n
  obtain ⟨w₀, hw₀, σ, hσ, hlim⟩ :=
    WeakDual.isSeqCompact_closedBall ℂ E (0 : StrongDual ℂ E) C hw
  let g : E := (InnerProductSpace.toDual ℂ E).symm w₀.toStrongDual
  have hg : ‖g‖ ≤ C := by
    have hn : ‖g‖ = ‖w₀.toStrongDual‖ :=
      (InnerProductSpace.toDual ℂ E).symm.norm_map _
    rw [hn]
    simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] using hw₀
  refine ⟨g, hg, σ, hσ, fun z => ?_⟩
  have h := ((WeakDual.eval_continuous z).tendsto w₀).comp hlim
  have heval : Tendsto (fun n => inner ℂ (u (σ n)) z) atTop
      (𝓝 (inner ℂ g z)) := by
    simpa only [Function.comp_apply, w, StrongDual.toWeakDual_apply,
      InnerProductSpace.toDual_apply_apply, g,
      InnerProductSpace.toDual_symm_apply] using h
  have hs := heval.star
  change Tendsto (fun n => starRingEnd ℂ (inner ℂ (u (σ n)) z)) atTop
    (𝓝 (starRingEnd ℂ (inner ℂ g z))) at hs
  simpa only [inner_conj_symm] using hs

/-- Both coordinate sequences use the same subsequence. The second
extraction refines the first, retaining its weak convergence. -/
theorem exists_two_bounded_weak_subsequences (u v : ℕ → E) (C : ℝ)
    (hu : ∀ n, ‖u n‖ ≤ C) (hv : ∀ n, ‖v n‖ ≤ C) :
    ∃ gx gy : E, ‖gx‖ ≤ C ∧ ‖gy‖ ≤ C ∧
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
        (∀ z, Tendsto (fun n => inner ℂ z (u (σ n))) atTop (𝓝 (inner ℂ z gx))) ∧
        (∀ z, Tendsto (fun n => inner ℂ z (v (σ n))) atTop (𝓝 (inner ℂ z gy))) := by
  obtain ⟨gx, hgx, σ, hσ, hx⟩ := exists_bounded_weak_subsequence u C hu
  obtain ⟨gy, hgy, τ, hτ, hy⟩ :=
    exists_bounded_weak_subsequence (fun n => v (σ n)) C (fun n => hv (σ n))
  exact ⟨gx, gy, hgx, hgy, σ ∘ τ, hσ.comp hτ,
    (fun z => (hx z).comp hτ.tendsto_atTop), hy⟩

end
end ImbalancedChen.Part3.HilbertBoundedWeakSubsequence20261026b
