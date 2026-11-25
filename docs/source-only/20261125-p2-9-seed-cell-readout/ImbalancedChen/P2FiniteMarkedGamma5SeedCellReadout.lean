import ImbalancedChen.P2FiniteMarkedGamma5OrderedOldSlots
import ImbalancedChen.P2FiniteMarkedGamma5SeedAtlasFinitePP
import ImbalancedChen.P2FiniteMarkedGamma5SelectedCellWallPayment

namespace ImbalancedChen.P2FiniteMarkedGamma5SeedCellReadout
noncomputable section
open Finset Real
open Part5OriginalCausalSmoothAtlas (Plan Code atom mask)
open Part5OriginalH430JointQueryEnclosure (Cube hit readout sharp_sandwich)
open Part5OriginalH430NativeQueryPaths (NativeSlot)
open Part5OriginalH430PhysicalRoots (Root)
open Part5OriginalH430SameQHistoryCells (cellQ)
open Part5OriginalH430FrozenRootRefinement (frozenLeafCutoffFloor frozenLeafCutoffFloor_pos)
open P2FiniteMarkedGamma5OrderedOldSlots (oldSlotEquiv)
open P2FiniteMarkedGamma5SeedAtlasFinitePP (Entry oldRank tailRank rank Tuple weight)
open P2FiniteMarkedGamma5EulerWordBudget (slotEquiv slotEquiv_old finPhysicalProfile)
open P2FiniteMarkedGamma5GateAffine (numbering)
open P2FiniteMarkedGamma5PhysicalExtension (Slot)
open P2FiniteMarkedGamma5AtlasFamily (atlasFamily_at_rank)
open P2FiniteMarkedGamma5AtlasEulerBudget (atlasProfile_eq_original_weight oldLogCoordinates)
open P2FiniteMarkedGamma5AllRankEulerBudget (scaleThreshold)
open P2FiniteMarkedGamma5SelectedCellAtlasStrips (cellSelected)
open P2FiniteMarkedGamma5SelectedNativeWallPayment (nativeLog)
open scoped Classical BigOperators

section reindex
variable {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ)

def pullSet (D : Set (κ → ℝ)) : Set (ι → ℝ) := {x | x ∘ e.symm ∈ D}

theorem atom_pull (P : Plan) (j : κ → Code P) (x : κ → ℝ) :
    atom P (j ∘ e) (x ∘ e) = atom P j x :=
  e.prod_comp (fun z => mask P (j z) (x z))

theorem hit_pull (P : Plan) (D : Set (κ → ℝ)) (j : κ → Code P) :
    hit P (pullSet e D) (j ∘ e) ↔ hit P D j := by
  constructor
  · rintro ⟨x,hx,hj,hD⟩
    refine ⟨x ∘ e.symm,fun z => hx (e.symm z),?_,hD⟩
    intro hz
    apply hj
    simpa only [Function.comp_def,Equiv.symm_apply_apply] using
      (atom_pull e P j (x ∘ e.symm)).trans hz
  · rintro ⟨x,hx,hj,hD⟩
    refine ⟨x ∘ e,fun z => hx (e z),?_,?_⟩
    · simpa only [atom_pull] using hj
    · simpa only [pullSet,Set.mem_setOf_eq,Function.comp_def,Equiv.apply_symm_apply] using hD

private def reindexCode (P : Plan) : (κ → Code P) ≃ (ι → Code P) where
  toFun j := j ∘ e
  invFun j := j ∘ e.symm
  left_inv j := by funext z; simp [Function.comp_def]
  right_inv j := by funext z; simp [Function.comp_def]

theorem readout_pull (P : Plan) (D : Set (κ → ℝ)) (x : κ → ℝ) :
    readout P (hit P (pullSet e D)) (x ∘ e) = readout P (hit P D) x := by
  unfold readout
  rw [← (reindexCode e P).sum_comp (fun j =>
    if hit P (pullSet e D) j then atom P j (x ∘ e) else 0)]
  apply sum_congr rfl
  intro j _
  change (if hit P (pullSet e D) (j ∘ e) then atom P (j ∘ e) (x ∘ e) else 0) = _
  simp only [hit_pull,atom_pull]

end reindex

/-- Every axis, including both fresh positions and every tail position, is
transported by the original numbering of the *same* Slot. -/
def wallTuple {N k r : ℕ} (u : Fin (k+(2+r)) → Fin (2*N+1)) :
    P2FiniteMarkedGamma5SelectedNativeWallPayment.Tuple N k r :=
  fun j => u (slotEquiv k r ((numbering k r).symm j))

@[simp] theorem wallTuple_numbering {N k r : ℕ}
    (u : Fin (k+(2+r)) → Fin (2*N+1)) (s : Slot k r) :
    wallTuple u (numbering k r s) = u (slotEquiv k r s) := by
  simp only [wallTuple,Equiv.symm_apply_apply]

def nativePoint {n N : ℕ} (v : Entry n) (u : Tuple N v) :
    NativeSlot v.val.1.val.1 → ℝ :=
  nativeLog v.val.1.val.1 (oldSlotEquiv v.val.1.val.1).symm
    (wallTuple (k:=oldRank v) (r:=tailRank v) u)

theorem ordered_logs {n N : ℕ} (v : Entry n) (u : Tuple N v) :
    oldLogCoordinates (k:=oldRank v) (r:=tailRank v) (N:ℝ) (fun i => ((u i).val:ℝ)) =
      nativePoint v u ∘ oldSlotEquiv v.val.1.val.1 := by
  funext i
  simp only [nativePoint,nativeLog,Function.comp_apply,Equiv.symm_apply_apply,
    wallTuple_numbering,slotEquiv_old]
  rfl

/-- The actual cell in native coordinates contains the old selected
history condition, root band, and cumulative root code. -/
def nativeDomain {n : ℕ} (v : Entry n) (root : Root) (tau : ℝ) :=
  cellSelected v.val.1.val.1 n root tau v.val.1.val.2 v.val.2.1

def planAt {n : ℕ} (m : P2FiniteMarkedGamma5NativeSeedSum.Index 430 → ℕ)
    (v : Entry n) : Plan := .mesh (m v.val.1)

/-- root, precision, tau, shape/read labels and mesh determine this
predicate before the target; the Family ABI includes an unused T. -/
def acceptAt {n : ℕ} (root : Root) (tau : ℝ)
    (m : P2FiniteMarkedGamma5NativeSeedSum.Index 430 → ℕ) (v : Entry n) (_T : ℕ) :
    (Fin (oldRank v) → Code (planAt m v)) → Prop :=
  hit (planAt m v) (pullSet (oldSlotEquiv v.val.1.val.1) (nativeDomain v root tau))

theorem actual_readout {n N : ℕ} (v : Entry n) (root : Root) (tau : ℝ)
    (m : P2FiniteMarkedGamma5NativeSeedSum.Index 430 → ℕ) (u : Tuple N v) :
    readout (planAt m v) (acceptAt root tau m v N)
      (oldLogCoordinates (k:=oldRank v) (r:=tailRank v) (N:ℝ) (fun i => ((u i).val:ℝ))) =
    readout (planAt m v) (hit (planAt m v) (nativeDomain v root tau)) (nativePoint v u) := by
  rw [ordered_logs]
  exact readout_pull _ _ _ _

theorem actual_weight {n N : ℕ} (v : Entry n) (root : Root) (tau : ℝ)
    (m : P2FiniteMarkedGamma5NativeSeedSum.Index 430 → ℕ) (u : Tuple N v)
    (width : ℝ) (hw : 0 < width) (hw1 : width ≤ 1)
    (hN : scaleThreshold frozenLeafCutoffFloor ≤ (N:ℝ)) (hN0 : 0 < N) :
    weight v (planAt m v) width frozenLeafCutoffFloor_pos hw hw1
      (acceptAt root tau m v) N u =
      finPhysicalProfile (log (cellQ N n v.val.2.1)) (N:ℝ) width
        ((N:ℝ)^frozenLeafCutoffFloor) (fun i => ((u i).val:ℝ)) *
      readout (planAt m v) (hit (planAt m v) (nativeDomain v root tau)) (nativePoint v u) := by
  unfold weight
  rw [atlasFamily_at_rank _ _ _ _ _ _ _ _ _ _ _ _ _ hN]
  rw [atlasProfile_eq_original_weight _ _ _ _ _
    (rpow_pos_of_pos (Nat.cast_pos.mpr hN0) frozenLeafCutoffFloor),actual_readout]

theorem sharp_cell_le_readout {n N : ℕ} (v : Entry n) (root : Root) (tau : ℝ)
    (m : P2FiniteMarkedGamma5NativeSeedSum.Index 430 → ℕ) (u : Tuple N v)
    (hc : Cube (nativePoint v u)) :
    (if nativePoint v u ∈ nativeDomain v root tau then (1:ℝ) else 0) ≤
      readout (planAt m v) (acceptAt root tau m v N)
        (oldLogCoordinates (k:=oldRank v) (r:=tailRank v) (N:ℝ)
          (fun i => ((u i).val:ℝ))) := by
  rw [actual_readout]
  exact (sharp_sandwich _ _ hc).2

end
end ImbalancedChen.P2FiniteMarkedGamma5SeedCellReadout
