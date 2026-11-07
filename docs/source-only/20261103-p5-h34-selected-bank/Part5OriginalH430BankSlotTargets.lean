import ImbalancedChen.Part5OriginalH430ClosedOwner
import ImbalancedChen.P5OriginalActionMassBound

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Bind the original 106 scalar slots to the existing 70 W1 / 36 W2 physical
parameter records. The closed finite guards below are proof bodies, not
premises and not previously executed checks. This binds target lists and
W1 labels only: it does not certify quadrature weights or switched bases.
-/
namespace ImbalancedChen.Part5OriginalH430BankSlotTargets

noncomputable section
open Set
open scoped Classical
open P2Selected430LiteralActionData (rows)
open P2Selected430CausalOccurrenceExporter
open P5OriginalActionMassBound
open Part5OriginalUpsilon5CausalDictionary
open Part5OriginalH430ClosedOwner Part5OriginalH430DecisionProvenance

/-- The original row order: ten anchors for each of seven W1 targets,
then the three original and thirty-three added W2 records. -/
def actionOfSlot (k : Fin 106) : Original106Action :=
  if h : k.val < 70 then
    .inl (⟨k.val / 10, by omega⟩, ⟨k.val % 10, Nat.mod_lt _ (by decide)⟩)
  else .inr ⟨k.val - 70, by omega⟩

def slotOfAction : Original106Action → Fin 106
  | .inl (i,j) => ⟨10*i.val+j.val, by have := i.isLt; have := j.isLt; omega⟩
  | .inr j => ⟨70+j.val, by have := j.isLt; omega⟩

theorem action_slot (a : Original106Action) : actionOfSlot (slotOfAction a) = a := by
  rcases a with ⟨i,j⟩ | j
  · have hi := i.isLt
    have hj := j.isLt
    have hk : 10*i.val+j.val < 70 := by omega
    simp only [slotOfAction, actionOfSlot, dif_pos hk]
    apply congrArg Sum.inl
    apply Prod.ext <;> apply Fin.ext <;> dsimp <;> omega
  · have hj := j.isLt
    simp only [slotOfAction, actionOfSlot, dif_neg (by omega : ¬70+j.val < 70)]
    apply congrArg Sum.inr
    apply Fin.ext
    dsimp
    omega

theorem slot_action (k : Fin 106) : slotOfAction (actionOfSlot k) = k := by
  by_cases hk : k.val < 70
  · simp only [actionOfSlot, dif_pos hk, slotOfAction]
    apply Fin.ext
    dsimp
    omega
  · simp only [actionOfSlot, dif_neg hk, slotOfAction]
    apply Fin.ext
    dsimp
    omega

def actionTarget : Original106Action → ℝ
  | .inl (i,_) => W1Target i
  | .inr j => (originalW2At j).s

/-- Exact integer target counts; each W2 target is on the original 1/50 grid. -/
def w2TargetCells : Fin 36 → ℕ :=
  ![60,60,55,51,52,53,54,55,55,56,57,58,60,60,62,62,64,65,
    66,66,68,70,72,72,74,75,76,78,78,80,82,84,84,86,88,90]

def targetCells (k : Fin 106) : ℕ :=
  if h : k.val < 70 then 70+5*(k.val/10)
  else w2TargetCells ⟨k.val-70, by omega⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- Closed integer/list check against the ORIGINAL literal rows.
UNEVALUATED until a Lean kernel run; no caller supplies this equality. -/
theorem literal_target_lists (k : Fin 106) :
    (rows k).targets = List.range (targetCells k) := by
  fin_cases k <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem literal_w1_labels (k : Fin 106) :
    (rows k).w1Label =
      match actionOfSlot k with
      | .inl ij => some ij
      | .inr _ => none := by
  fin_cases k <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- The integer target metadata is connected to the existing REAL records,
not to a second unattached transcription of their parameters. -/
theorem targetCells_real (k : Fin 106) :
    floorGrid (targetCells k) = actionTarget (actionOfSlot k) := by
  fin_cases k <;>
    norm_num [targetCells, w2TargetCells, actionOfSlot, actionTarget,
      W1Target, originalW2At, originalRepairedW2Bank, floorGrid]

theorem target_positive (a : Original106Action) : 0 < actionTarget a := by
  rcases a with ⟨i,j⟩ | j
  · have hi : (0:ℝ) ≤ i.val := Nat.cast_nonneg _
    dsimp [actionTarget, W1Target]
    linarith
  · fin_cases j <;> norm_num [actionTarget, originalW2At, originalRepairedW2Bank]

theorem W1_target_le_anchor (i : Fin 7) (j : Fin 10) :
    W1Target i ≤ W1Anchor j := by
  have hi : (i.val:ℝ) ≤ 6 := by exact_mod_cast (show i.val ≤ 6 by omega)
  have hj : (0:ℝ) ≤ j.val := Nat.cast_nonneg _
  dsimp [W1Target, W1Anchor]
  linarith

/-- The fixed W2 comparisons are after its target for every original row. -/
theorem W2_target_le_fixed (j : Fin 36) (anchor : Bool) :
    (originalW2At j).s ≤
      (if anchor then (originalW2At j).s0 else (originalW2At j).phi1) := by
  fin_cases j <;> cases anchor <;>
    norm_num [originalW2At, originalRepairedW2Bank]

theorem targetCell_right_le {k : Fin 106} {i : Fin 200}
    (hi : i.val ∈ (rows k).targets) :
    floorGrid (i.val+1) ≤ actionTarget (actionOfSlot k) := by
  rw [literal_target_lists, List.mem_range] at hi
  rw [← targetCells_real]
  have hcast : ((i.val+1:ℕ):ℝ) ≤ targetCells k := by exact_mod_cast (show i.val+1 ≤ targetCells k by omega)
  dsimp [floorGrid]
  linarith

/-- A literal selected bank slot supplies the actual parent target test.
The closed owner is still selected using the NEW table. -/
theorem selected_bank_target {g : Fin 430} {up : Bool} {b : FloorAtom}
    {s : ℝ} {k : Fin 106} (hb : s ∈ P5OriginalFeedbackTableKernels.tableAtomSet (!up) b)
    (hk : selectedChoice g up b = .bank k) :
    up = true ∧ s ≤ actionTarget (actionOfSlot k) := by
  have ha := selected_allowed g up b
  rw [hk] at ha
  change up = true ∧ (selectedOwner g up b).val ∈ (rows k).targets at ha
  have hs := selected_owner_contains hb
  rw [queryCell_eq_grid] at hs
  exact ⟨ha.1, hs.2.trans (targetCell_right_le ha.2)⟩

end
end ImbalancedChen.Part5OriginalH430BankSlotTargets
