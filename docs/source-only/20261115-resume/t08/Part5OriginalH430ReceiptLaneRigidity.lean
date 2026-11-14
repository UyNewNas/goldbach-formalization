import ImbalancedChen.Part5OriginalH430FirstReceiptExit
import ImbalancedChen.Part5OriginalH430SelectedMemberBox

/-!
Exact full/selected count binding for the ORIGINAL root receiver mask.
Only positions whose integer word is still [p] carry root receipts.
All genuinely appended positions have empty root-receipt intersection;
their ordinary frozen source, positive mark and Theta are NOT deleted.

SOURCE_ONLY / UNCOMPILED.  This diagnoses the scope of root-mask
inheritance; it does not supply ordinary/switched estimates or h34.
-/
namespace ImbalancedChen.Part5OriginalH430ReceiptLaneRigidity

noncomputable section
open scoped Classical BigOperators
open Part5OriginalUpsilon5CausalDictionary (a)
open P2EnhancedLowerPhysicalNode
open P2EnhancedLowerPrimeChildCarriers (parentProduct physicalPrime)
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2FrozenReceiverCountActions (frozenCount)
open P5OriginalU5FrozenSource (receiver)
open P5OriginalActionMassBound (Original106Action)
open P2OriginalLiteralW1OldProfile (cutoff_eq_physical_power)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport Part5OriginalH430SameQHistoryCells
open Part5OriginalH430RequestedHistory Part5OriginalH430RequestedMember
open Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430TaggedArithmeticReceivers Part5OriginalH430OwnedRootCounts
open Part5OriginalH430OriginalReceiptMemberPullback
open Part5OriginalH430SelectedMemberBox Part5OriginalH430FirstReceiptExit

private theorem unit_lane {N p : ℕ} {z : ℝ} (hz : z ≤ (N : ℝ)^a) :
    originalReceiptLane N p 1 z = originalReceiver N p := by
  ext q
  constructor
  · exact fun hq => (Finset.mem_filter.mp hq).1
  · intro hq
    refine Finset.mem_filter.mpr ⟨hq,one_dvd _,?_⟩
    rw [Nat.div_one]
    exact fun r hr hd => hz.trans ((Finset.mem_filter.mp hq).2 r hr hd)

/-- The actual old word, rather than depth, detects the first receipt
exit: retained and fixed comparisons may have positive depth and still
have word [p].  Both root labels use their OWN frozen Q and owner. -/
theorem actual_member_lane {N n m p : ℕ} {k : Root} {t : ℝ}
    {c : RootKey n m} {o : Occurrence N} (hN : 2 ≤ N) (ht : 0 ≤ t)
    (hu : t ≤ 1/12) (hn : 1/((n : ℝ)+1) ≤ 11/384)
    (hp : p ∈ rootFibre N n m k t c) (ho : o ∈ rootHistory N n k t p) :
    originalReceiptLane N p (tailProduct o) (memberCutoff (cellQ N n c.1) o) =
      if o.current.old = [p] then originalReceiver N p else ∅ := by
  have hband := (Finset.mem_filter.mp hp).1
  obtain ⟨xs,hw,hstate⟩ := actual_history_receipt_state hN ht hu hn hband ho
  have htail : tailProduct o = xs.prod := by simp only [tailProduct,hw,List.tail_cons]
  have hsmall (q : ℕ) (hq : q ∈ xs) (hpr : q.Prime)
      (hqa : (q : ℝ) < (N : ℝ)^a) :
      originalReceiptLane N p (tailProduct o) (memberCutoff (cellQ N n c.1) o) = ∅ := by
    apply originalReceiptLane_empty_of_small _ hpr _ hqa
    rw [htail]
    exact List.dvd_prod hq
  by_cases hsame : o.current.old = [p]
  · rw [if_pos hsame]
    have hxs : xs = [] := (List.cons.inj (hw.symm.trans hsame)).2
    have hcap : residual o.current.node.physical ≤ a*o.current.node.physical.argument := by
      rcases hstate with h | ⟨q,hq,_,_⟩
      · exact h.2.2
      · simp only [hxs,List.not_mem_nil] at hq
    have hsup := rootHistory_support (by omega : 1 < N) ht hu hn
      (original_band_prime hband) (original_band_geometry hN hband) ho
    dsimp only at hsup
    have hQ := (original_fibre_geometry hN ht hu hn hp).1
    have hz : memberCutoff (cellQ N n c.1) o ≤ (N : ℝ)^a := by
      rw [memberCutoff,hQ,cutoff_eq_physical_power hsup.1.2.1 hsup.2.2.2.2.2]
      apply Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast (show 1 ≤ N by omega) : (1 : ℝ) ≤ N)
      apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hsup.2.2.2.1.1)).mpr
      rw [← hsup.2.1]
      exact hcap
    rw [htail,hxs,List.prod_nil]
    exact unit_lane hz
  · rw [if_neg hsame]
    rcases hstate with ⟨hxs,_,_⟩ | ⟨q,hq,hpr,hqa⟩
    · exact False.elim (hsame (by simpa only [hxs] using hw))
    · exact hsmall q hq hpr hqa

/-- The full ordinary count at an appended occurrence is EXACTLY its
named rejectedChild mass. This is not an error bound and not a zero
statement about that ordinary source. -/
theorem appended_member_ordinary_is_rejected {N n m p : ℕ} {k : Root} {t : ℝ}
    {c : RootKey n m} {o : Occurrence N} (hN : 2 ≤ N) (ht : 0 ≤ t)
    (hu : t ≤ 1/12) (hn : 1/((n : ℝ)+1) ≤ 11/384)
    (hp : p ∈ rootFibre N n m k t c) (ho : o ∈ rootHistory N n k t p)
    (hproper : o.current.old ≠ [p]) :
    (frozenCount N (parentProduct o.current.old) (receiver N)
      (memberCutoff (cellQ N n c.1) o) : ℝ) =
    ((rejectedChild N (parentProduct o.current.old) (tailProduct o)
      (memberCutoff (cellQ N n c.1) o)).card : ℝ) := by
  have h := actual_member_count_split hN ht hu hn hp ho
  dsimp only at h
  rw [actual_member_lane hN ht hu hn hp ho,if_neg hproper,
    Finset.card_empty,Nat.cast_zero,zero_add] at h
  exact h

theorem actual_member_masked_count {N n m p : ℕ} {k : Root} {t : ℝ}
    {c : RootKey n m} {o : Occurrence N} (hN : 2 ≤ N) (ht : 0 ≤ t)
    (hu : t ≤ 1/12) (hn : 1/((n : ℝ)+1) ≤ 11/384)
    (hp : p ∈ rootFibre N n m k t c) (ho : o ∈ rootHistory N n k t p) :
    (frozenCount N (parentProduct o.current.old) (rootMask N p)
      (memberCutoff (cellQ N n c.1) o) : ℝ) =
      if o.current.old = [p] then ((originalReceiver N p).card : ℝ) else 0 := by
  rw [owned_member_masked_count hN ht hu hn hp ho,actual_member_lane hN ht hu hn hp ho]
  split_ifs <;> simp only [Finset.card_empty,Nat.cast_zero]

/-- Positive weight of the original, unextended positions, preserving
every list position, predecessor and owner. It is not set to one. -/
def rankOneWeight {N n p G : ℕ} {k : Root} {t : ℝ}
    (S : Finset (LevelIndex N n k t p G)) : ℝ :=
  ∑ l ∈ S.filter (fun l => (levelOccurrence l).current.old = [p]), levelMark l

theorem rankOneWeight_nonneg {N n p G : ℕ} {k : Root} {t : ℝ}
    (S : Finset (LevelIndex N n k t p G)) : 0 ≤ rankOneWeight S := by
  apply Finset.sum_nonneg
  intro l _
  exact (mark_pos (levelOccurrence l)).le

/-- Any actual subfamily at ONE remaining generation, including a
complete level or the literal selected bank/box filter. No Member or
abstract counting premise is accepted in place of the generated list. -/
theorem masked_position_sum {N n m p G : ℕ} {k : Root} {t : ℝ}
    {c : RootKey n m} (S : Finset (LevelIndex N n k t p G))
    (hN : 2 ≤ N) (ht : 0 ≤ t) (hu : t ≤ 1/12)
    (hn : 1/((n : ℝ)+1) ≤ 11/384) (hp : p ∈ rootFibre N n m k t c) :
    (∑ l ∈ S, levelMark l * (frozenCount N
      (parentProduct (levelOccurrence l).current.old) (rootMask N p)
      (memberCutoff (cellQ N n c.1) (levelOccurrence l)) : ℝ)) =
      ((originalReceiver N p).card : ℝ) * rankOneWeight S := by
  rw [rankOneWeight,Finset.mul_sum,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro l _
  rw [actual_member_masked_count hN ht hu hn hp (levelOccurrence_source l).1]
  by_cases h : (levelOccurrence l).current.old = [p] <;> simp [h,mul_comm]

/-- The complete 0..430 generation and all original selected bank boxes
are specializations of the same count identity with the same root key.
Different generations are never added together. -/
theorem complete_level_masked_count {N n m : ℕ} (k : Root) {t : ℝ}
    (G : Fin 431) (c : RootKey n m) (hN : 2 ≤ N) (ht : 0 ≤ t)
    (hu : t ≤ 1/12) (hn : 1/((n : ℝ)+1) ≤ 11/384) :
    (∑ p ∈ rootFibre N n m k t c, ∑ l : LevelIndex N n k t p G.val,
      levelMark l * (frozenCount N (parentProduct (levelOccurrence l).current.old)
        (rootMask N p) (memberCutoff (cellQ N n c.1) (levelOccurrence l)) : ℝ)) =
    ∑ p ∈ rootFibre N n m k t c,
      ((originalReceiver N p).card : ℝ) *
        rankOneWeight (Finset.univ : Finset (LevelIndex N n k t p G.val)) := by
  apply Finset.sum_congr rfl
  intro p hp
  exact masked_position_sum Finset.univ hN ht hu hn hp

theorem selected_box_masked_count {N n m mesh : ℕ} (k : Root) {t : ℝ}
    (g : Fin 430) (act : Original106Action) (c : RootKey n m) (b : Box mesh)
    (hN : 2 ≤ N) (ht : 0 ≤ t) (hu : t ≤ 1/12)
    (hn : 1/((n : ℝ)+1) ≤ 11/384) :
    boxMasked N n m mesh k t g act c b =
    ∑ p ∈ rootFibre N n m k t c,
      ((originalReceiver N p).card : ℝ) *
        rankOneWeight (positions N n mesh k t p g act b) := by
  unfold boxMasked
  apply Finset.sum_congr rfl
  intro p hp
  exact masked_position_sum _ hN ht hu hn hp

end
end ImbalancedChen.Part5OriginalH430ReceiptLaneRigidity
