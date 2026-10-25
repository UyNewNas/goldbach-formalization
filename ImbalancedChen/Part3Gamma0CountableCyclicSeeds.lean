import ImbalancedChen.Part3Gamma0QuotientL2Separable
import ImbalancedChen.Part3Gamma0ActualGlobalFriedrichsGraph
import Mathlib.Topology.Bases

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
Nonzero mutually orthogonal cyclic seeds in ACTUAL Gamma0 quotient L2
form a countable set. The actual Hilbert separability is constructed in
the preceding module. Pythagoras gives disjoint nonempty open balls, so
the pinned separable-space disjoint-open-family theorem proves countability.
The existing actual resolvent, generic Zorn family and actual spectral
index are reused exactly; no whole-plane space or new global unitary
is substituted and no hCountable/hSeparable premise occurs.
-/

namespace ImbalancedChen.Part3.Gamma0CountableCyclicSeeds20261025a
noncomputable section
open Set MeasureTheory
open scoped Classical
open Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualWeakRieszResolvent20261025a
open Gamma0ActualGlobalFriedrichsGraph20261025a
open GenericResolventGlobalSpectralAssembly20261025a

/-- Every nonzero pairwise orthogonal set in a separable complex inner
product space is countable; no uniform lower norm bound is needed. -/
theorem nonzero_pairwise_orthogonal_countable
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [TopologicalSpace.SeparableSpace H] {s : Set H}
    (horth : s.Pairwise (fun f g => inner ℂ f g = 0))
    (hne : ∀ f ∈ s, f ≠ 0) : s.Countable := by
  have hd : s.PairwiseDisjoint (fun f => Metric.ball f (‖f‖ / 2)) := by
    intro f hf g hg hfg
    have hinner : inner ℂ f (-g) = 0 := by simp [horth hf hg hfg]
    have hpyth : ‖f - g‖ ^ 2 = ‖f‖ ^ 2 + ‖g‖ ^ 2 := by
      simpa only [sub_eq_add_neg, norm_neg, pow_two] using
        norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero f (-g) hinner
    have hfbound : ‖f‖ ≤ ‖f - g‖ :=
      (sq_le_sq₀ (norm_nonneg f) (norm_nonneg (f - g))).mp
        (by nlinarith [sq_nonneg ‖g‖])
    have hgbound : ‖g‖ ≤ ‖f - g‖ :=
      (sq_le_sq₀ (norm_nonneg g) (norm_nonneg (f - g))).mp
        (by nlinarith [sq_nonneg ‖f‖])
    apply Metric.ball_disjoint_ball
    rw [dist_eq_norm]
    linarith
  apply hd.countable_of_isOpen (fun _ _ => Metric.isOpen_ball)
  intro f hf
  refine ⟨f, Metric.mem_ball_self ?_⟩
  exact div_pos (norm_pos_iff.mpr (hne f hf)) (by norm_num)

/-- A cyclic seed belongs to its OWN genuine closed CFC orbit. Thus
orthogonality of the actual cyclic subspaces implies seed orthogonality. -/
theorem orthogonalCyclicSeeds_countable
    (N : ℕ) [NeZero N] (R : QuotientL2 N →L[ℂ] QuotientL2 N) (hSA : IsSelfAdjoint R)
    (s : Set (QuotientL2 N)) (hs : OrthogonalCyclicSeeds R hSA s) : s.Countable := by
  apply nonzero_pairwise_orthogonal_countable ?_ hs.2
  intro f hf g hg hfg
  exact (hs.1 hf hg hfg).inner_eq
    (self_mem_cyclicSubspace R hSA f) (self_mem_cyclicSubspace R hSA g)

/-- Countability for the physical Gamma0 R=J J*, with its actual proved
self-adjointness, not an operator supplied to replace that resolvent. -/
theorem actual_orthogonalCyclicSeeds_countable (N : ℕ) [NeZero N]
    (s : Set (QuotientL2 N))
    (hs : OrthogonalCyclicSeeds (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N) s) :
    s.Countable :=
  orthogonalCyclicSeeds_countable N (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N) s hs

theorem actual_spectralCyclicSeeds_countable (N : ℕ) [NeZero N] :
    (spectralCyclicSeeds (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N)).Countable :=
  actual_orthogonalCyclicSeeds_countable N _
    (spectralCyclicSeeds_orthogonal (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N))

/-- The EXACT index already used by the actual global Friedrichs graph
is countable; the existing Zorn assembly is not rebuilt or renamed. -/
instance actualSpectralIndex_countable (N : ℕ) [NeZero N] : Countable (ActualSpectralIndex N) :=
  (actual_spectralCyclicSeeds_countable N).to_subtype

/-- The genuine actual maximal TOTAL cyclic family can be chosen
countable, with maximality and totality both conclusions of the supplier. -/
theorem exists_countable_maximal_total_actual_cyclic_family (N : ℕ) [NeZero N] :
    ∃ s : Set (QuotientL2 N), s.Countable ∧
      OrthogonalCyclicSeeds (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N) s ∧
      (∀ t, s ⊆ t →
        OrthogonalCyclicSeeds (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N) t → t = s) ∧
      (cyclicFamilySpan (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N) s).topologicalClosure = ⊤ := by
  obtain ⟨s, hs, hmax, htotal⟩ :=
    exists_maximal_total_cyclic_family (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N)
  exact ⟨s, actual_orthogonalCyclicSeeds_countable N s hs, hs, hmax, htotal⟩

end
end ImbalancedChen.Part3.Gamma0CountableCyclicSeeds20261025a
