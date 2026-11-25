import ImbalancedChen.P2OriginalLowerWholeBoxBranchSelect
import ImbalancedChen.P2OriginalCompactPhysicalGateTransfer

-- SOURCE ONLY / UNCOMPILED_ZERO_CREDIT / HELD.
-- A selected tent branch's own support mask is transported from strict
-- whole-box square tests to the actual compact physical exponent word.
-- Trace.marked is NOT the branch mask. The finite bank and its original
-- factorization licence remain separate, uninstantiated inputs.

namespace ImbalancedChen.P2OriginalSelectedMaskPhysicalSquares

noncomputable section
open scoped Classical
open P2PhysicalIncomingPrefixCells P2LowerCapPlanIntegerRetention
open P2EnhancedLowerPhysicalNode
open P2OriginalLowerSelectedCapConstructor (Code BranchTable prefixCode)
open P2OriginalLowerCompactStartCapConstructor
open P2OriginalLowerCompactTraceBinding
open P2OriginalLowerWholeBoxBranchSelect
open P2OriginalCompactPhysicalGateTransfer

private theorem squareGates_mono {cap T U : ℝ}
    {xs ys : List ℝ} (hTU : T ≤ U)
    (hxy : List.Forall₂ (· ≤ ·) xs ys)
    (hy : SquareGates cap U ys) : SquareGates cap T xs := by
  induction hxy generalizing T U with
  | nil => trivial
  | @cons x y xs ys hxy htail ih =>
      rcases hy with ⟨hhead, hrest⟩
      constructor
      · linarith
      · exact ih (add_le_add hTU hxy) hrest

private theorem sum_le_of_forall₂ {xs ys : List ℝ}
    (hxy : List.Forall₂ (· ≤ ·) xs ys) : xs.sum ≤ ys.sum := by
  induction hxy with
  | nil => simp
  | @cons x y xs ys hxy htail ih =>
      simp only [List.sum_cons]
      linarith

private theorem slots_exponents_le {xs ys : List Slot}
    (h : List.Forall₂
      (fun p q : Slot => p.exponent ≤ q.exponent ∧ p.selected = q.selected)
      xs ys) :
    List.Forall₂ (· ≤ ·) (xs.map Slot.exponent)
      (ys.map Slot.exponent) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | @cons p q ps qs hp htail ih =>
      exact List.Forall₂.cons hp.1 ih

private theorem slots_selected_le {xs ys : List Slot}
    (h : List.Forall₂
      (fun p q : Slot => p.exponent ≤ q.exponent ∧ p.selected = q.selected)
      xs ys) :
    List.Forall₂ (· ≤ ·) (selectedWord xs) (selectedWord ys) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | @cons p q ps qs hp htail ih =>
      by_cases hs : p.selected = true
      · have hq : q.selected = true := by rw [← hp.2]; exact hs
        simpa [selectedWord, hs, hq] using List.Forall₂.cons hp.1 ih
      · have hq : q.selected ≠ true := by
          intro hq
          exact hs (hp.2.trans hq)
        simpa [selectedWord, hs, hq] using ih

private theorem slots_remaining_le {xs ys : List Slot}
    (h : List.Forall₂
      (fun p q : Slot => p.exponent ≤ q.exponent ∧ p.selected = q.selected)
      xs ys) :
    List.Forall₂ (· ≤ ·) (remainingWord xs) (remainingWord ys) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | @cons p q ps qs hp htail ih =>
      by_cases hs : p.selected = true
      · have hq : q.selected = true := by rw [← hp.2]; exact hs
        simpa [remainingWord, hs, hq] using ih
      · have hq : q.selected ≠ true := by
          intro hq
          exact hs (hp.2.trans hq)
        simpa [remainingWord, hs, hq] using List.Forall₂.cons hp.1 ih

def pointSlot (S : CompactStart) {mesh : ℕ}
    (code : Code mesh) (mask : Finset (Fin 5))
    (x : Fin 5 → ℝ) (i : Fin 5) : Slot :=
  ⟨x i, (code i).2 || decide (i ∈ mask)⟩

def pointPrefixSlots (S : CompactStart) {mesh : ℕ}
    (rank : Fin 6) (code : Code mesh)
    (mask : Finset (Fin 5)) (x : Fin 5 → ℝ) : List Slot :=
  match rank.val with
  | 3 => [pointSlot S code mask x 0, pointSlot S code mask x 1,
      pointSlot S code mask x 2]
  | 4 => [pointSlot S code mask x 0, pointSlot S code mask x 1,
      pointSlot S code mask x 2, pointSlot S code mask x 3]
  | 5 => [pointSlot S code mask x 0, pointSlot S code mask x 1,
      pointSlot S code mask x 2, pointSlot S code mask x 3,
      pointSlot S code mask x 4]
  | _ => []

-- Future masked slots can be padded by none without affecting a prefix;
-- their upper endpoint is w, which still bounds the actual compact word.
theorem actual_below_prefix_upper (S : CompactStart) {mesh : ℕ}
    (rank : Fin 6) (x : Fin 5 → ℝ)
    (hx : ∀ i, x i ∈ Set.Icc (S.epsilon : ℝ)
      (startCutoff S.start : ℝ)) :
    ∀ i, x i ≤ P2OriginalCompactPhysicalGateTransfer.upper S
      (prefixCode rank.val (actualCode S mesh x)) i := by
  intro i
  by_cases hi : i.val < rank.val
  · simpa [P2OriginalCompactPhysicalGateTransfer.upper,
      prefixCode, hi] using
        actual_five_word_below_upper S x hx i
  · have htop := (hx i).2
    simpa [P2OriginalCompactPhysicalGateTransfer.upper,
      prefixCode, hi,
      P2OriginalLowerCompactStartCapConstructor.cellUpper] using htop

private theorem point_slots_le_own_upper (S : CompactStart) {mesh : ℕ}
    (rank : Fin 6) (code : Code mesh)
    (mask : Finset (Fin 5)) (x : Fin 5 → ℝ)
    (hupper : ∀ i, x i ≤
      P2OriginalCompactPhysicalGateTransfer.upper S code i) :
    List.Forall₂
      (fun p q : Slot => p.exponent ≤ q.exponent ∧ p.selected = q.selected)
      (pointPrefixSlots S rank code mask x)
      (ownPrefixSlots S rank code mask) := by
  fin_cases rank <;>
    simp [pointPrefixSlots, ownPrefixSlots, pointSlot, ownSlot,
      P2OriginalCompactPhysicalGateTransfer.upper, hupper]

-- The selected support comes from SourceForm.supportMask, NEVER from the
-- all-false marks of the ordinary Trace. Both complete and selected
-- square tests now hold on the same actual point as the chosen source.
theorem selected_source_actual_square_gates (S : CompactStart)
    {mesh : ℕ} (bank : CandidateBank mesh) (buffer : ℚ)
    (rank : Fin 6) (x : Fin 5 → ℝ)
    (hx : ∀ i, x i ∈ Set.Icc (S.epsilon : ℝ)
      (startCutoff S.start : ℝ))
    (data : P2OriginalLowerBufferedAffineBoxes.BranchData)
    (hsel : select S bank buffer rank
      (prefixCode rank.val (actualCode S mesh x)) = some data) :
    ∃ b ∈ bank.alternatives rank
        (prefixCode rank.val (actualCode S mesh x)),
      supportCheck S rank
        (prefixCode rank.val (actualCode S mesh x)) buffer b ∧
      data = b.asBranchData ∧
      let code := prefixCode rank.val (actualCode S mesh x)
      let pts := pointPrefixSlots S rank code b.form.supportMask x
      let cap := (bufferedCap S code buffer b : ℝ)
      SquareGates cap 0 (pts.map Slot.exponent) ∧
        SquareGates cap (selectedWord pts).sum (remainingWord pts) := by
  obtain ⟨b, hb, hcheck, hdata⟩ :=
    select_some_source S bank buffer rank (actualCode S mesh x)
      data hsel
  refine ⟨b, hb, hcheck, hdata, ?_⟩
  let code := prefixCode rank.val (actualCode S mesh x)
  let pts := pointPrefixSlots S rank code b.form.supportMask x
  let ups := ownPrefixSlots S rank code b.form.supportMask
  let cap := (bufferedCap S code buffer b : ℝ)
  have hslot : List.Forall₂
      (fun p q : Slot => p.exponent ≤ q.exponent ∧ p.selected = q.selected)
      pts ups :=
    point_slots_le_own_upper S rank code b.form.supportMask x
      (actual_below_prefix_upper S rank x hx)
  obtain ⟨hfull, hselected⟩ :=
    supportCheck_has_own_mask_gates S rank code buffer b hcheck
  have hfullUpper : SquareGates cap 0 (ups.map Slot.exponent) :=
    P2OriginalLowerSelectedCapConstructor.strictSquareGates_sound cap 0 _ hfull
  have hselectedUpper :
      SquareGates cap (selectedWord ups).sum (remainingWord ups) :=
    P2OriginalLowerSelectedCapConstructor.strictSquareGates_sound cap _ _ hselected
  have hfullPoint := squareGates_mono (le_refl (0 : ℝ))
    (slots_exponents_le hslot) hfullUpper
  have hselectedPoint := squareGates_mono
    (sum_le_of_forall₂ (slots_selected_le hslot))
    (slots_remaining_le hslot) hselectedUpper
  exact ⟨hfullPoint, hselectedPoint⟩

-- The same selected bank supplies the support mask and the scalar table.
-- The fourth historical admission still reads H.cap, the frozen third cap;
-- the selected mask is used only for the square tests, not Trace.marked.
theorem selected_fourth_source_and_incoming_trace (S : CompactStart)
    {mesh : ℕ} (bank : CandidateBank mesh) (buffer : ℚ)
    (rho : ℝ) (x : Fin 5 → ℝ)
    (hx : ∀ i, x i ∈ Set.Icc (S.epsilon : ℝ)
      (startCutoff S.start : ℝ))
    (hsmall : rho < (249 / 448 : ℝ) - 3 * (19 / 125 : ℝ))
    (data : P2OriginalLowerBufferedAffineBoxes.BranchData)
    (hsel : select S bank buffer 4
      (prefixCode 4 (actualCode S mesh x)) = some data)
    (hthird : ∃ c s : ℝ,
      checkedChoice S
        (P2OriginalLowerCompactStartCapConstructor.boxedTable S
          (select S bank buffer) buffer)
        3 (baselineCap rho) (actualCode S mesh x) = .fresh c s)
    (hfourth : ∃ c s : ℝ,
      checkedChoice S
        (P2OriginalLowerCompactStartCapConstructor.boxedTable S
          (select S bank buffer) buffer)
        4 (cap3 S
          (P2OriginalLowerCompactStartCapConstructor.boxedTable S
            (select S bank buffer) buffer)
          rho (actualCode S mesh x))
        (actualCode S mesh x) = .fresh c s)
    (H : Trace) (hword : H.word = [x 0, x 1, x 2])
    (hincoming : H.cap = cap3 S
      (P2OriginalLowerCompactStartCapConstructor.boxedTable S
        (select S bank buffer) buffer)
      rho (actualCode S mesh x))
    (haccepted : H.accepted = true) :
    (∃ b ∈ bank.alternatives 4
        (prefixCode 4 (actualCode S mesh x)),
      supportCheck S 4 (prefixCode 4 (actualCode S mesh x))
        buffer b ∧ data = b.asBranchData ∧
      let code := prefixCode 4 (actualCode S mesh x)
      let pts := pointPrefixSlots S 4 code b.form.supportMask x
      let cap := (bufferedCap S code buffer b : ℝ)
      SquareGates cap 0 (pts.map Slot.exponent) ∧
        SquareGates cap (selectedWord pts).sum (remainingWord pts)) ∧
    (step (compactPlan S
      (P2OriginalLowerCompactStartCapConstructor.boxedTable S
        (select S bank buffer) buffer) rho)
      (S.epsilon : ℝ) (startCutoff S.start : ℝ)
      H (x 3)).accepted = true := by
  let table := P2OriginalLowerCompactStartCapConstructor.boxedTable S
    (select S bank buffer) buffer
  have hsquares := selected_source_actual_square_gates S bank buffer 4 x
    hx data hsel
  have hpass := selected_fourth_actual_trace_passes S table rho x hx
    hsmall hthird hfourth H hword hincoming haccepted
  exact ⟨hsquares, hpass⟩

end
end ImbalancedChen.P2OriginalSelectedMaskPhysicalSquares
