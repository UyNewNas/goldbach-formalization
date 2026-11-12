import ImbalancedChen.Part5OriginalH430SelectedMemberBox

/-! One actual query for each occupied selected prime box. Keep the clamp
at two and the genuine least-prime shell when the child query changes.
No unproved payment or common fixed query across different boxes. -/
namespace ImbalancedChen.Part5OriginalH430SelectedMemberFixedQuery
noncomputable section
open scoped Classical BigOperators
open P5OriginalActionMassBound (Original106Action)
open P2EnhancedLowerPhysicalTransition (gridArgument)
open P2EnhancedLowerPrimeChildCarriers (parentProduct)
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2FrozenReceiverCountActions (frozenCount frozen_selected_buchstab markedPhi)
open Wu2008DoubleSieve (primeWindow)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenIntegerSupport
open Part5OriginalH430SameQHistoryCells Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedMember Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430TaggedArithmeticReceivers Part5OriginalH430OwnedRootCounts
open Part5OriginalH430ActualResolvedPhysicalGates
open Part5OriginalH430OriginalReceiptMemberPullback Part5OriginalH430SelectedMemberBox

def fixedQuery {mesh : ℕ} (b : Box mesh) : ℝ :=
  if b.1.2 then 2 else
    match b.2.2 with
    | none => 6
    | some i => gridArgument i

theorem occupied_query {N n m mesh p : ℕ} {k : Root} {t : ℝ} {g : Fin 430}
    {act : Original106Action} {c : RootKey n m} {b : Box mesh} {l : Index N n k t p g}
    (hN : 2 ≤ N) (ht : 0 ≤ t) (hu : t ≤ 1/12) (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p ∈ rootFibre N n m k t c) (hl : l ∈ positions N n mesh k t p g act b) :
    (levelOccurrence l).current.node.physical.argument ≤ fixedQuery b ∧
      ((levelOccurrence l).current.node.physical.argument = 2 → fixedQuery b = 2) := by
  obtain ⟨i,⟨hi,hcell⟩,_⟩ := (occupied_member_owner hN ht hu hn hp hl).2.1
  have hclamp : b.1.2 = decide ((levelOccurrence l).current.node.physical.argument = 2) := by
    rw [← (Finset.mem_filter.mp hl).2]
    rfl
  by_cases h : (levelOccurrence l).current.node.physical.argument = 2
  · have hw : fixedQuery b = 2 := by simp [fixedQuery,hclamp,h]
    exact ⟨h.le.trans_eq hw.symm,fun _ => hw⟩
  · have hw : fixedQuery b = gridArgument i := by simp [fixedQuery,hclamp,h,hi]
    exact ⟨(show (levelOccurrence l).current.node.physical.argument ≤ gridArgument i
      from hcell.2).trans_eq hw.symm,fun he => (h he).elim⟩

def queryShell {N : ℕ} (Q : ℝ) (p : ℕ) (o : Occurrence N) (w : ℝ) : ℝ :=
  let B := parentProduct o.current.old
  ∑ r ∈ primeWindow (B*N) (cutoff Q B w) (memberCutoff Q o),
    (frozenCount N (B*r) (rootMask N p) (r:ℝ) : ℝ)

/-- Positive marked Phi with *one* fixed Q and s on an original selected
box equals its original-root-compatible receipt count plus the explicit
new least-prime shell. The original additive-prime predicate remains the
same at B and at B*r. Other receipt lanes and analytic prices are separate. -/
theorem fixed_query_original_receipts {N n m mesh : ℕ} (k : Root) {t : ℝ}
    (g : Fin 430) (act : Original106Action) (c : RootKey n m) (b : Box mesh)
    (hN : 4 ≤ N) (ht : 0 ≤ t) (hu : t ≤ 1/12) (hn : 1/((n:ℝ)+1) ≤ 11/384) :
    let Q := cellQ N n c.1
    (∑ p ∈ rootFibre N n m k t c, markedPhi N Q (positions N n mesh k t p g act b)
      (fun l => parentProduct (levelOccurrence l).current.old) (fun l => levelMark l)
      (fun _ => rootMask N p) (fixedQuery b)) =
      (∑ p ∈ rootFibre N n m k t c, ∑ q ∈ originalReceiver N p,
        receiptMark N n mesh k t p g act b Q q) +
      ∑ p ∈ rootFibre N n m k t c, ∑ l ∈ positions N n mesh k t p g act b,
        levelMark l * queryShell Q p (levelOccurrence l) (fixedQuery b) := by
  dsimp only
  rw [← box_count_on_original_receipts k g act c b (by omega : 2≤N) ht hu hn]
  unfold boxMasked
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  unfold markedPhi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l hl
  let Q := cellQ N n c.1
  let o := levelOccurrence l
  let B := parentProduct o.current.old
  have hband := (Finset.mem_filter.mp hp).1
  have hp' := original_band_prime hband
  have hb := original_band_geometry (by omega : 2≤N) hband
  have hq := (original_fibre_geometry (by omega : 2≤N) ht hu hn hp).1
  have hR : 1 < Q/(B:ℝ) := by
    dsimp only [Q,B,o]
    rw [hq]
    exact actual_level_quotient_gt_one N n k t p g l hN ht hu hn hp' hb
  have hs := (rootHistory_support (by omega : 1<N) ht hu hn hp' hb
    (levelOccurrence_source l).1).2.2.2.1
  have hsw := (occupied_query (by omega : 2≤N) ht hu hn hp hl).1
  have hcut : cutoff Q B (fixedQuery b) ≤ memberCutoff Q o :=
    Real.rpow_le_rpow_of_exponent_le hR.le
      (one_div_le_one_div_of_le (zero_lt_one.trans_le hs.1) hsw)
  have hZ := frozen_selected_buchstab N B (rootMask N p) hcut
  have hreal : (frozenCount N B (rootMask N p) (cutoff Q B (fixedQuery b)) : ℝ) =
      (frozenCount N B (rootMask N p) (memberCutoff Q o) : ℝ) +
        queryShell Q p o (fixedQuery b) := by
    unfold queryShell
    exact_mod_cast hZ
  change levelMark l * (frozenCount N B (rootMask N p) (cutoff Q B (fixedQuery b)) : ℝ) = _
  rw [hreal,mul_add]

end
end ImbalancedChen.Part5OriginalH430SelectedMemberFixedQuery
