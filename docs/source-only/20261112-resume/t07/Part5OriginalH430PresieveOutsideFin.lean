import ImbalancedChen.Part5OriginalH430OriginalTagSeparatedFinSource
import ImbalancedChen.Part5OriginalH430RequestedOriginalRowFreeze

/-! The beta presieve in the manuscript is below every active cutoff.
At any actual frozen U3 or U4 root, this places every original selected p
outside the small-prime list. Compute the resulting full tagged Fin weights
and the four outside terms without discarding an arithmetic occurrence. -/
namespace ImbalancedChen.Part5OriginalH430PresieveOutsideFin
noncomputable section
open scoped Classical BigOperators
open P2EnhancedLowerPrimeChildCarriers (physicalPrime)
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open Part5OriginalUpsilon5CausalDictionary (a)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport Part5OriginalH430RequestedOriginalRowFreeze
open Part5OriginalH430TaggedArithmeticReceivers Part5OriginalH430TaggedReceiverFibres
open Part5OriginalH430ReceiverRootGateAccounting Part5OriginalH430OriginalRootCutoffObstruction
open Part5OriginalH430ActualRootGateCoprime Part5OriginalH430OriginalSelectedRootFibres
open Part5OriginalH430PhysicalSelectedRootQFibres Part5OriginalH430ActualRootStageReceipts
open Part5OriginalH430TaggedRankTwoFibreCapacity Part5OriginalH430PhysicalSlotCollisionLedger
open Part5OriginalH430PhysicalSlotListPositions Part5OriginalH430FixedQSlotInjection
open Part5OriginalH430FullTaggedActualFinPushforward Part5OriginalH430FourLaneFullTaggedFin

theorem presieve_below_frozen_root {N n p : ℕ} {k : Root} {τ z₀ : ℝ}
    (hN : 2 ≤ N) (hτ : 0 ≤ τ) (hτ' : τ ≤ 1 / 12)
    (hn : 1 / ((n : ℝ) + 1) ≤ 11 / 384) (hp : p ∈ originalBand N k)
    (hz : z₀ ≤ cutoff (rootQ N n k τ p) p
      (frozenRoot n k τ (physicalPrime N p)).physical.argument) :
    z₀ ≤ (N : ℝ) ^ a := by
  apply hz.trans
  unfold cutoff
  rw [frozen_root_sameQ_cutoff_power N n p k τ hN (original_band_prime hp).1.pos
    hτ hτ' (original_band_geometry hN hp) hn]
  exact Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast (show 1 ≤ N by omega)) (min_le_left _ _)

/-- The observed source at every physical Q and every actual list position
is zero. The original two-tag source is entirely in the cutoff-blocked
term, including the boundary p = z₀. No condition is placed on its
integer quotient or on the sign of the transported weight. -/
theorem full_tagged_fin_at_manuscript_presieve {N cap n p : ℕ} {k : Root} {τ z₀ : ℝ}
    (hN : 2 ≤ N) (hτ : 0 ≤ τ) (hτ' : τ ≤ 1 / 12)
    (hn : 1 / ((n : ℝ) + 1) ≤ 11 / 384) (hp : p ∈ originalBand N k)
    (hz : z₀ ≤ cutoff (rootQ N n k τ p) p
      (frozenRoot n k τ (physicalPrime N p)).physical.argument)
    (hcap : z₀ ≤ (cap : ℝ)) (lower : Bool) :
    (∀ (w : TaggedReceiver → ℝ) (Q : ℝ)
      (i : Fin (actualPhysicalRankTwoList N cap z₀ Q lower).length),
      actualAllTaggedAtFin N cap n τ z₀ lower w Q i = 0) ∧
    rootCutoffBlocked (originalTagged N) z₀ = originalTagged N ∧
    (∀ w : TaggedReceiver → ℝ,
      originalFourOutsidePositionLanes N cap n τ z₀ lower w =
        ∑ z ∈ originalTagged N, w z) := by
  have hs := presieve_below_frozen_root hN hτ hτ' hn hp hz
  have hstage : (originalTagged N).filter
      (selectedOriginalRootStage N cap n τ z₀ lower) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro z hm
    obtain ⟨ho, hi⟩ := Finset.mem_filter.mp hm
    exact (not_lt_of_ge hs)
      (actual_original_stage_requires_large_presieve N cap n τ z₀ lower hcap ho hi)
  have hslots : observedPhysicalSlots N cap n τ z₀ lower = ∅ := by
    simp only [observedPhysicalSlots, observedRankTwoKeys, retainedReceipts, hstage,
      Finset.filter_empty, Finset.image_empty]
  have hfin (w : TaggedReceiver → ℝ) (Q : ℝ)
      (i : Fin (actualPhysicalRankTwoList N cap z₀ Q lower).length) :
      actualAllTaggedAtFin N cap n τ z₀ lower w Q i = 0 := by
    apply actual_all_tagged_fin_zero_outside_slots
    rintro ⟨s, _⟩
    have hm := s.property
    simpa [observedPhysicalSlotsAtQ, hslots] using hm
  have hpolicy : physicalPolicyBlocked N n τ z₀ lower = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro z hm
    obtain ⟨ho, hi, _⟩ := Finset.mem_filter.mp hm
    exact raw_root_no_strict_cutoff N z₀ hs (original_tagged_subset_raw_unconditional N ho) hi
  have hcut := original_selected_all_cutoff_if_small N z₀ hs
  refine ⟨hfin, hcut, ?_⟩
  intro w
  simp [originalFourOutsidePositionLanes, hstage, hcut, hpolicy]

end
end ImbalancedChen.Part5OriginalH430PresieveOutsideFin
