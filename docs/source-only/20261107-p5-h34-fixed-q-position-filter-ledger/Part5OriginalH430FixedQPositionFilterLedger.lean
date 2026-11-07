import ImbalancedChen.Part5OriginalH430FixedQSlotInjection
import ImbalancedChen.FirstExitFrontierAdmission

/-!
P5.6/h34: filter the actual fixed-Q rank-two LIST POSITIONS, not
deduplicated state values. A finite position gate can erase an
observed physical (Q,p,ell) slot: every such erasure remains explicit.
Survivors inject into the kept Fin positions, not into q/tag receipts.
The real ordinary Rosser complete-prefix test used by this same
frontier is instantiated separately, and is shown to erase nothing.
The complete manuscript full/selected/inherited count gates and
payments remain OPEN; a generic Boolean gate is not their licence.
SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL H34 OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430FixedQPositionFilterLedger

noncomputable section
open scoped Classical BigOperators
open Part5OriginalH430PhysicalSlotListPositions
open Part5OriginalH430FixedQSlotInjection

abbrev SlotAtQ (N cap precision : ℕ) (tau z0 : ℝ)
    (lower : Bool) (Q : ℝ) :=
  {slot : ℝ × ℕ × ℕ //
    slot ∈ observedPhysicalSlotsAtQ N cap precision tau z0 lower Q}

/-- True original rank-two LIST occurrence positions that pass the
given explicit post-frontier test, with duplicate positions intact. -/
def keptPositions (N cap : ℕ) (z0 Q : ℝ) (lower : Bool)
    (keep : FirstExitDepthState ℕ → Bool) :
    Finset (Fin (actualPhysicalRankTwoList N cap z0 Q lower).length) :=
  Finset.univ.filter (fun i =>
    keep ((actualPhysicalRankTwoList N cap z0 Q lower)[i]) = true)

/-- Real observed slots whose chosen actual list occurrence survives. -/
def keptSlots (N cap precision : ℕ) (tau z0 : ℝ)
    (lower : Bool) (Q : ℝ) (keep : FirstExitDepthState ℕ → Bool) :
    Finset (SlotAtQ N cap precision tau z0 lower Q) :=
  Finset.univ.filter (fun s =>
    keep ((actualPhysicalRankTwoList N cap z0 Q lower)[
      fixedQSlotPositionMap N cap precision tau z0 lower Q s]) = true)

/-- Deleted observed physical slots still contribute to the source. -/
def erasedSlots (N cap precision : ℕ) (tau z0 : ℝ)
    (lower : Bool) (Q : ℝ) (keep : FirstExitDepthState ℕ → Bool) :
    Finset (SlotAtQ N cap precision tau z0 lower Q) :=
  Finset.univ.filter (fun s =>
    keep ((actualPhysicalRankTwoList N cap z0 Q lower)[
      fixedQSlotPositionMap N cap precision tau z0 lower Q s]) = false)

theorem kept_erased_union (N cap precision : ℕ) (tau z0 : ℝ)
    (lower : Bool) (Q : ℝ) (keep : FirstExitDepthState ℕ → Bool) :
    keptSlots N cap precision tau z0 lower Q keep ∪
      erasedSlots N cap precision tau z0 lower Q keep =
        Finset.univ := by
  classical
  ext s
  simp only [Finset.mem_union, keptSlots, erasedSlots,
    Finset.mem_filter, Finset.mem_univ, true_and]
  cases h : keep ((actualPhysicalRankTwoList N cap z0 Q lower)[
    fixedQSlotPositionMap N cap precision tau z0 lower Q s]) <;>
    simp [h]

theorem kept_erased_disjoint (N cap precision : ℕ) (tau z0 : ℝ)
    (lower : Bool) (Q : ℝ) (keep : FirstExitDepthState ℕ → Bool) :
    Disjoint (keptSlots N cap precision tau z0 lower Q keep)
      (erasedSlots N cap precision tau z0 lower Q keep) := by
  apply Finset.disjoint_left.mpr
  intro s hs he
  have hyes := (Finset.mem_filter.mp hs).2
  have hno := (Finset.mem_filter.mp he).2
  rw [hyes] at hno
  cases hno

/-- Exact full physical SLOT count: kept plus unpaid deleted. -/
theorem observed_slot_erasure_card (N cap precision : ℕ) (tau z0 : ℝ)
    (lower : Bool) (Q : ℝ) (keep : FirstExitDepthState ℕ → Bool) :
    (observedPhysicalSlotsAtQ N cap precision tau z0 lower Q).card =
      (keptSlots N cap precision tau z0 lower Q keep).card +
      (erasedSlots N cap precision tau z0 lower Q keep).card := by
  classical
  have h := Finset.card_union_of_disjoint
    (kept_erased_disjoint N cap precision tau z0 lower Q keep)
  rw [kept_erased_union N cap precision tau z0 lower Q keep] at h
  simpa [SlotAtQ] using h

/-- Arbitrarily signed slot weights, including deleted slot weights,
remain exact; no sign cancellation is used to claim a bound. -/
theorem observed_slot_erasure_signed (N cap precision : ℕ)
    (tau z0 : ℝ) (lower : Bool) (Q : ℝ)
    (keep : FirstExitDepthState ℕ → Bool)
    (w : ℝ × ℕ × ℕ → ℝ) :
    (∑ s : SlotAtQ N cap precision tau z0 lower Q, w s.1) =
      (∑ s ∈ keptSlots N cap precision tau z0 lower Q keep, w s.1) +
      (∑ s ∈ erasedSlots N cap precision tau z0 lower Q keep, w s.1) := by
  classical
  calc
    (∑ s : SlotAtQ N cap precision tau z0 lower Q, w s.1) =
        ∑ s ∈ keptSlots N cap precision tau z0 lower Q keep ∪
          erasedSlots N cap precision tau z0 lower Q keep, w s.1 := by
            rw [kept_erased_union N cap precision tau z0 lower Q keep]
    _ = _ := Finset.sum_union
      (kept_erased_disjoint N cap precision tau z0 lower Q keep)

/-- Actual Fin occurrence map restricted to surviving source slots. -/
def keptPositionMap (N cap precision : ℕ) (tau z0 : ℝ)
    (lower : Bool) (Q : ℝ) (keep : FirstExitDepthState ℕ → Bool) :
    {s : SlotAtQ N cap precision tau z0 lower Q //
      s ∈ keptSlots N cap precision tau z0 lower Q keep} →
    {i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length //
      i ∈ keptPositions N cap z0 Q lower keep} := by
  intro s
  refine ⟨fixedQSlotPositionMap N cap precision tau z0 lower Q s.1, ?_⟩
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, (Finset.mem_filter.mp s.2).2⟩

theorem kept_position_injective (N cap precision : ℕ)
    (tau z0 : ℝ) (lower : Bool) (Q : ℝ)
    (keep : FirstExitDepthState ℕ → Bool) :
    Function.Injective (keptPositionMap
      N cap precision tau z0 lower Q keep) := by
  intro s t heq
  apply Subtype.ext
  exact fixed_q_slot_position_injective
    N cap precision tau z0 lower Q
    (congrArg Subtype.val heq)

/-- Kept slots fit into genuine surviving LIST positions. -/
theorem kept_slots_le_kept_positions (N cap precision : ℕ)
    (tau z0 : ℝ) (lower : Bool) (Q : ℝ)
    (keep : FirstExitDepthState ℕ → Bool) :
    (keptSlots N cap precision tau z0 lower Q keep).card ≤
      (keptPositions N cap z0 Q lower keep).card := by
  classical
  have hb :
      Fintype.card {s : SlotAtQ N cap precision tau z0 lower Q //
        s ∈ keptSlots N cap precision tau z0 lower Q keep} ≤
      Fintype.card {i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length //
        i ∈ keptPositions N cap z0 Q lower keep} :=
    Fintype.card_le_of_injective
      (keptPositionMap N cap precision tau z0 lower Q keep)
      (kept_position_injective N cap precision tau z0 lower Q keep)
  simpa using hb

/-- No deleted slot disappears from the capacity side. -/
theorem slot_capacity_with_erasure (N cap precision : ℕ)
    (tau z0 : ℝ) (lower : Bool) (Q : ℝ)
    (keep : FirstExitDepthState ℕ → Bool) :
    (observedPhysicalSlotsAtQ N cap precision tau z0 lower Q).card ≤
      (keptPositions N cap z0 Q lower keep).card +
      (erasedSlots N cap precision tau z0 lower Q keep).card := by
  have hs := observed_slot_erasure_card
    N cap precision tau z0 lower Q keep
  have hk := kept_slots_le_kept_positions
    N cap precision tau z0 lower Q keep
  omega

/-- Only the ACTUAL complete-prefix ordinary Rosser gate already
built into the rank-two recursion, not the count-source gates. -/
def actualFullPrefixGate (lower : Bool) (Q : ℝ)
    (s : FirstExitDepthState ℕ) : Bool :=
  decide (ordinaryRosserPrefixAdmissible lower Q s.selectedPrefix)

/-- Every actual rank-two list occurrence passed the same policy. -/
theorem actual_rank_two_full_prefix_passes (N cap : ℕ)
    (z0 Q : ℝ) (lower : Bool)
    (i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length) :
    actualFullPrefixGate lower Q
      ((actualPhysicalRankTwoList N cap z0 Q lower)[i]) = true := by
  have hm : (actualPhysicalRankTwoList N cap z0 Q lower)[i] ∈
      actualPhysicalRankTwoList N cap z0 Q lower := by
    exact List.getElem_mem
  have hv := mem_firstExitDepthFrontier_ordinaryRosser_admissible_of_pos
    lower Q 2 (by decide)
    (fun r : ℕ => 1 / ((r : ℝ) - 1))
    (roughPrimeUniverse N cap 0 z0)
    ((actualPhysicalRankTwoList N cap z0 Q lower)[i])
    (by simpa only [actualPhysicalRankTwoList] using hm)
  exact decide_eq_true hv

/-- This ONE real full-prefix gate never erases the preexisting
rank-two list positions. Other gates remain to be instantiated. -/
theorem actual_full_prefix_keeps_positions (N cap : ℕ)
    (z0 Q : ℝ) (lower : Bool) :
    keptPositions N cap z0 Q lower (actualFullPrefixGate lower Q) =
      Finset.univ := by
  classical
  ext i
  have hi := actual_rank_two_full_prefix_passes N cap z0 Q lower i
  simp [keptPositions, hi]

theorem actual_full_prefix_erases_no_observed_slots
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool) (Q : ℝ) :
    erasedSlots N cap precision tau z0 lower Q
      (actualFullPrefixGate lower Q) = ∅ := by
  classical
  ext s
  have hs := actual_rank_two_full_prefix_passes N cap z0 Q lower
    (fixedQSlotPositionMap N cap precision tau z0 lower Q s)
  simp [erasedSlots, hs]

end
end ImbalancedChen.Part5OriginalH430FixedQPositionFilterLedger
