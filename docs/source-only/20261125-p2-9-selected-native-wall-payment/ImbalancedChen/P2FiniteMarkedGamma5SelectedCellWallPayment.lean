import ImbalancedChen.P2FiniteMarkedGamma5SelectedNativeWallPayment
import ImbalancedChen.P2FiniteMarkedGamma5SelectedCellAtlasStrips

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The original full wall list also pays the fixed-root-code atlas domains.
Every root code and tail rank is included in one finite error budget.
-/
namespace ImbalancedChen.P2FiniteMarkedGamma5SelectedCellWallPayment
noncomputable section
open Filter Finset Real Set
open P2EnhancedLowerPhysicalTransition (StepShape)
open Part5OriginalH430NativeQueryPaths (NativeSlot)
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430FrozenRootRefinement (RootCode rootCode)
open Part5OriginalH430TaggedArithmeticReceivers (originalBand)
open Part5OriginalCausalSmoothAtlas Part5OriginalH430JointQueryEnclosure
open P2FiniteMarkedGamma5FixedNativeItinerary (ReadLabel)
open P2FiniteMarkedGamma5SelectedNativeStrips (Space)
open P2FiniteMarkedGamma5SelectedCellAtlasStrips (cellSelected)
open P2FiniteMarkedGamma5SelectedNativeWallPayment
open P2FiniteMarkedGamma5GateAffine (numbering)
open P2FiniteMarkedGamma5RadialRoughMass (norm)
open scoped Classical BigOperators Topology

variable {depth k : ℕ} (sh : Fin depth → StepShape) (e : NativeSlot sh ≃ Fin k)

/-- The literal comparison retains the original strict root band,
the selected native predicate, and the original cumulative root code. -/
def cellOuterTuples (N n : ℕ) (root : Root) (tau : ℝ)
    (labels : Fin depth → ReadLabel) (c : RootCode n) (r m : ℕ) :
    Finset (Tuple N k r) :=
  (baseTuples N k r).filter fun u =>
    readout (.mesh m) (hit (.mesh m) (cellSelected sh n root tau labels c))
      (nativeLog sh e u) ≠ 0 ∧
    ¬ ((u (numbering k r (.inl (e (.inl ()))))).val ∈ originalBand N root ∧
      nativeLog sh e u ∈ P2FiniteMarkedGamma5RealSelectedPrefix.selected n root tau sh labels ∧
      rootCode n (sourceRoot root tau (nativeLog sh e u (.inl ()))).physical.total = c)

/-- A single mesh covers every root code, target and tail rank. The
strict original upper endpoint is paid by the existing exact zero row. -/
theorem exists_cell_outer_cover (n : ℕ) (root : Root) (labels : Fin depth → ReadLabel)
    (hn : 1/((n : ℝ)+1) ≤ 11/384) {delta : ℝ} (hd : 0 < delta) :
    ∃ m : ℕ, ∀ N : ℕ, 2 ≤ N → ∀ tau : ℝ, 0 ≤ tau → tau ≤ 1/12 →
      ∀ c : RootCode n, ∀ r : ℕ,
      cellOuterTuples sh e N n root tau labels c r m ⊆
        nativeWallTuples sh e N n root labels r delta := by
  obtain ⟨m,H⟩ := P2FiniteMarkedGamma5SelectedCellAtlasStrips.fine_outer_strip
    sh n root labels hd hn
  refine ⟨m,?_⟩
  intro N hN tau ht ht' c r u hu
  obtain ⟨hb,hout,hfail⟩ := mem_filter.mp hu
  apply mem_filter.mpr
  refine ⟨hb,?_⟩
  by_cases hclosed : nativeLog sh e u ∈ cellSelected sh n root tau labels c
  · have hp : ∀ i, (u i).val.Prime := (mem_filter.mp (mem_filter.mp hb).1).2
    have hcop := (mem_filter.mp hb).2.2.2
    let j := numbering k r (.inl (e (.inl ())))
    have hroot : (u j).val.Prime ∧ (u j).val.Coprime N :=
      ⟨hp j,hcop.of_dvd_left (dvd_prod_of_mem (fun i => (u i).val) (mem_univ j))⟩
    have hnot : (u j).val ∉ originalBand N root :=
      fun h => hfail ⟨h,hclosed.1.2,hclosed.2⟩
    obtain ⟨q,hq,hnz,hzero⟩ := original_root_zero_wall sh n root labels
      (nativeLog sh e u) hN hroot rfl hclosed.1.1 hnot
    exact ⟨q,hq,hnz,by rw [hzero,abs_zero]; exact hd.le⟩
  · exact H tau ht ht' c (nativeLog sh e u) (nativeLog_cube sh e hN hb) hclosed hout

/-- One ordinary epsilon pays the entire finite root-code and tail-rank
sum. In particular, no epsilon is spent separately at a moving prime,
history position, or code chosen after the target. -/
theorem exists_all_cells_outer_payment (n : ℕ) (root : Root)
    (labels : Fin depth → ReadLabel) (hn : 1/((n : ℝ)+1) ≤ 11/384)
    (K : ℕ) {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ m : ℕ, ∀ᶠ N : ℕ in atTop, ∀ tau : ℝ, 0 ≤ tau → tau ≤ 1/12 →
      norm N * (∑ c : RootCode n, ∑ r : Fin (K+1),
        ((cellOuterTuples sh e N n root tau labels c r.val m).card : ℝ)) ≤ epsilon := by
  let C : ℝ := Fintype.card (RootCode n)
  let eta := epsilon / (C+1)
  have hC : 0 ≤ C := Nat.cast_nonneg _
  have hden : 0 < C+1 := by linarith
  have heta : 0 < eta := div_pos he hden
  obtain ⟨delta,hd,Hpaid⟩ := exists_finite_tail_wall_payment sh e n root labels K heta
  obtain ⟨m,Hcover⟩ := exists_cell_outer_cover sh e n root labels hn hd
  refine ⟨m,?_⟩
  filter_upwards [Hpaid,eventually_ge_atTop (2 : ℕ)] with N hpaid hN
  intro tau ht ht'
  have hnrm : 0 ≤ norm N :=
    div_nonneg (log_nonneg (by exact_mod_cast (show 1 ≤ N by omega)))
      (Nat.cast_nonneg _)
  calc
    _ = ∑ c : RootCode n, norm N * (∑ r : Fin (K+1),
        ((cellOuterTuples sh e N n root tau labels c r.val m).card : ℝ)) := mul_sum ..
    _ ≤ ∑ _c : RootCode n, eta := by
      apply sum_le_sum
      intro c hc
      apply le_trans (mul_le_mul_of_nonneg_left ?_ hnrm) hpaid
      apply sum_le_sum
      intro r hr
      exact Nat.cast_le.mpr (card_le_card (Hcover N hN tau ht ht' c r.val))
    _ = C * eta := by simp [C]
    _ ≤ (C+1) * eta := mul_le_mul_of_nonneg_right (by linarith) heta.le
    _ = epsilon := by
      dsimp only [eta]
      rw [mul_comm,div_mul_cancel₀ _ hden.ne']

end
end ImbalancedChen.P2FiniteMarkedGamma5SelectedCellWallPayment
