import ImbalancedChen.P2OriginalCompositeTentSelector
import ImbalancedChen.P2OriginalLowerWThirdPhysicalRow

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The old selected-subproduct supportCheck deliberately rejects every W form.
This module does not weaken it. A mixed rank-three bank keeps screened tent
rows and the independently licensed original W(t3) row as different sources.
The preliminary screen, rho and W buffers are fixed before selection.
Inherited is tested first. A crossing box is left unselected for trimming.
No global retained cover, factorization theorem or final CapPlan is assumed.
-/

namespace ImbalancedChen.P2OriginalMixedThirdWTentSelector

noncomputable section
open scoped Classical
open P2PhysicalIncomingPrefixCells
open P2OriginalLowerAffineTieSelector P2OriginalLowerBufferedAffineBoxes
open P2OriginalLowerSelectedCapConstructor (Code prefixCode)
open P2OriginalLowerCompactStartCapConstructor
open P2OriginalLowerWholeBoxBranchSelect
open P2OriginalCompositeTentSelector
open P2OriginalLowerWThirdPhysicalRow

-- All 31 nonempty five-slot masks have labels at most 31. The W label
-- is separate from every mask label and has empty selected support.
def wRow (S : CompactStart) {mesh : ℕ} (code : Code mesh)
    (buffer : ℚ) : SelectedBranchData :=
  ⟨32, .wSlot 2, wQueryLower S code buffer⟩

theorem wRow_no_selected_mask (S : CompactStart) {mesh : ℕ}
    (code : Code mesh) (buffer : ℚ) :
    (wRow S code buffer).form.supportMask = ∅ := rfl

-- The row stores the unbuffered affine source, but its licence and query
-- are checked at its separately buffered rational W cap.
def mixedRows (S : CompactStart) {mesh : ℕ} (rho : ℝ)
    (screen buffer delta : ℚ)
    (argument : Fin 6 → Code mesh → SourceForm → ℚ)
    (code : Code mesh) : List SelectedBranchData :=
  compositeAlternatives S screen argument 3 code ++
    (if WBoxCheck S code rho buffer delta then
      [wRow S code buffer] else [])

theorem mixedRows_source (S : CompactStart) {mesh : ℕ} (rho : ℝ)
    (screen buffer delta : ℚ)
    (argument : Fin 6 → Code mesh → SourceForm → ℚ)
    (code : Code mesh) (b : SelectedBranchData)
    (hb : b ∈ mixedRows S rho screen buffer delta argument code) :
    (∃ mask ∈ P2OriginalFiniteTentBankSelectorMargins.tentMasks 3,
      lowerSide S 3 code argument mask = some b ∧
      supportCheck S 3 code screen b) ∨
    (b = wRow S code buffer ∧ WBoxCheck S code rho buffer delta) := by
  rcases List.mem_append.mp hb with ht | hw
  · exact Or.inl (compositeAlternatives_screened S screen argument 3 code b ht)
  · by_cases hW : WBoxCheck S code rho buffer delta
    · have heq : b = wRow S code buffer := by
        simpa only [if_pos hW, List.mem_singleton] using hw
      exact Or.inr ⟨heq, hW⟩
    · simp only [if_neg hW, List.not_mem_nil] at hw

-- Only affine order is tested here. Licensing was established while
-- forming mixedRows: a tent has supportCheck, W has WBoxCheck instead.
def dominates (box : RationalBox) (base : LabeledBranch 5)
    (rows : List SelectedBranchData) (b : SelectedBranchData) : Prop :=
  (b.cap = base.cap ∨ 0 < gapLower b.cap base.cap box) ∧
    ∀ c ∈ rows, b.cap = c.cap ∨ 0 < gapLower b.cap c.cap box

def mixedWinner (S : CompactStart) {mesh : ℕ} (rho : ℝ)
    (screen buffer delta : ℚ)
    (inherited : Code mesh → LabeledBranch 5)
    (argument : Fin 6 → Code mesh → SourceForm → ℚ)
    (code : Code mesh) : Option SelectedBranchData :=
  let pc := prefixCode 3 code
  let rows := mixedRows S rho screen buffer delta argument pc
  let box := boxOfCode S pc
  if stableBase box (inherited pc) rows then none
  else firstStable (dominates box (inherited pc) rows) rows

theorem mixedWinner_future_invariant (S : CompactStart) {mesh : ℕ}
    (rho : ℝ) (screen buffer delta : ℚ)
    (inherited : Code mesh → LabeledBranch 5)
    (argument : Fin 6 → Code mesh → SourceForm → ℚ)
    {code₁ code₂ : Code mesh}
    (h : ∀ i : Fin 5, i.val < 3 → code₁ i = code₂ i) :
    mixedWinner S rho screen buffer delta inherited argument code₁ =
      mixedWinner S rho screen buffer delta inherited argument code₂ := by
  have hp := P2OriginalLowerSelectedCapConstructor.prefixCode_future_invariant h
  simp only [mixedWinner, hp]

theorem mixedWinner_some (S : CompactStart) {mesh : ℕ} (rho : ℝ)
    (screen buffer delta : ℚ)
    (inherited : Code mesh → LabeledBranch 5)
    (argument : Fin 6 → Code mesh → SourceForm → ℚ)
    (code : Code mesh) (b : SelectedBranchData)
    (h : mixedWinner S rho screen buffer delta inherited argument code = some b) :
    b ∈ mixedRows S rho screen buffer delta argument (prefixCode 3 code) ∧
      dominates (boxOfCode S (prefixCode 3 code))
        (inherited (prefixCode 3 code))
        (mixedRows S rho screen buffer delta argument (prefixCode 3 code)) b := by
  unfold mixedWinner at h
  split at h
  · simp at h
  · exact firstStable_some h

theorem mixedWinner_source (S : CompactStart) {mesh : ℕ} (rho : ℝ)
    (screen buffer delta : ℚ)
    (inherited : Code mesh → LabeledBranch 5)
    (argument : Fin 6 → Code mesh → SourceForm → ℚ)
    (code : Code mesh) (b : SelectedBranchData)
    (h : mixedWinner S rho screen buffer delta inherited argument code = some b) :
    (∃ mask ∈ P2OriginalFiniteTentBankSelectorMargins.tentMasks 3,
      lowerSide S 3 (prefixCode 3 code) argument mask = some b ∧
      supportCheck S 3 (prefixCode 3 code) screen b) ∨
    (b = wRow S (prefixCode 3 code) buffer ∧
      WBoxCheck S (prefixCode 3 code) rho buffer delta) := by
  exact mixedRows_source S rho screen buffer delta argument
    (prefixCode 3 code) b (mixedWinner_some S rho screen buffer delta
      inherited argument code b h).1

private theorem dominates_eval (a b : AffineBranch 5)
    (box : RationalBox) (x : Fin 5 → ℝ) (hx : inBox box x)
    (h : a = b ∨ 0 < gapLower a b box) : b.eval x ≤ a.eval x := by
  rcases h with heq | hgap
  · rw [heq]
  · have hpoint := gapLower_le_eval_gap a b box x hx
    have hcast : (0 : ℝ) < gapLower a b box := by exact_mod_cast hgap
    linarith

-- Maxima are taken between complete source actions. The two tent sides
-- have already been minimized within each mask by compositeAlternatives.
theorem mixedWinner_pointwise_max (S : CompactStart) {mesh : ℕ}
    (rho : ℝ) (screen buffer delta : ℚ)
    (inherited : Code mesh → LabeledBranch 5)
    (argument : Fin 6 → Code mesh → SourceForm → ℚ)
    (code : Code mesh) (b : SelectedBranchData)
    (h : mixedWinner S rho screen buffer delta inherited argument code = some b)
    (x : Fin 5 → ℝ) (hx : inBox (boxOfCode S (prefixCode 3 code)) x) :
    (inherited (prefixCode 3 code)).cap.eval x ≤ b.cap.eval x ∧
    ∀ c ∈ mixedRows S rho screen buffer delta argument (prefixCode 3 code),
      c.cap.eval x ≤ b.cap.eval x := by
  have hs := (mixedWinner_some S rho screen buffer delta
    inherited argument code b h).2
  exact ⟨dominates_eval _ _ _ x hx hs.1,
    fun c hc => dominates_eval _ _ _ x hx (hs.2 c hc)⟩

theorem mixedWinner_inherited_first (S : CompactStart) {mesh : ℕ}
    (rho : ℝ) (screen buffer delta : ℚ)
    (inherited : Code mesh → LabeledBranch 5)
    (argument : Fin 6 → Code mesh → SourceForm → ℚ)
    (code : Code mesh)
    (h : stableBase (boxOfCode S (prefixCode 3 code))
      (inherited (prefixCode 3 code))
      (mixedRows S rho screen buffer delta argument (prefixCode 3 code))) :
    mixedWinner S rho screen buffer delta inherited argument code = none := by
  simp only [mixedWinner, if_pos h]

-- The selected W case returns the exact separately licensed physical
-- row and the corresponding fresh checked choice, without asserting a
-- tent supportCheck for W or rechecking against an ideal parent cap.
theorem mixedWinner_W_physical_row (S : CompactStart) {mesh : ℕ}
    (rho : ℝ) (screen buffer delta : ℚ)
    (inherited : Code mesh → LabeledBranch 5)
    (argument : Fin 6 → Code mesh → SourceForm → ℚ)
    (code : Code mesh)
    (h : mixedWinner S rho screen buffer delta inherited argument code =
      some (wRow S (prefixCode 3 code) buffer)) :
    WBoxCheck S (prefixCode 3 code) rho buffer delta ∧
    (WThirdTable S rho buffer delta).row 3 (prefixCode 3 code) =
      some (wCap S (prefixCode 3 code) buffer,
        wQueryLower S (prefixCode 3 code) buffer) := by
  rcases mixedWinner_source S rho screen buffer delta
    inherited argument code (wRow S (prefixCode 3 code) buffer) h with ht | hw
  · obtain ⟨mask, _, hside, _⟩ := ht
    rcases lowerSide_is_tent S 3 (prefixCode 3 code) argument mask
      (wRow S (prefixCode 3 code) buffer) hside with hl | hr
    · change SourceForm.wSlot 2 = SourceForm.tentLeft mask at hl
      cases hl
    · change SourceForm.wSlot 2 = SourceForm.tentRight mask at hr
      cases hr
  · exact ⟨hw.2, WThirdTable_row S rho buffer delta (prefixCode 3 code) hw.2⟩


private theorem firstStable_eq_of_unique {rows : List SelectedBranchData}
    {P : SelectedBranchData → Prop} {b : SelectedBranchData}
    (hb : b ∈ rows) (hPb : P b)
    (hunique : ∀ c ∈ rows, P c → c = b) :
    firstStable P rows = some b := by
  induction rows with
  | nil => cases hb
  | cons c cs ih =>
      by_cases hc : P c
      · have hcb : c = b := hunique c List.mem_cons_self hc
        subst c
        simp only [firstStable, if_pos hPb]
      · have hbcs : b ∈ cs := by
          rcases List.mem_cons.mp hb with hbc | hbcs
          · subst c
            exact False.elim (hc hPb)
          · exact hbcs
        have htail : ∀ d ∈ cs, P d → d = b := by
          intro d hd hPd
          exact hunique d (List.mem_cons_of_mem _ hd) hPd
        simpa only [firstStable, if_neg hc] using ih hbcs htail

-- This proves selection from an independently checked strict affine
-- chamber; it does not assume a selected policy or the winner equality.
-- The physical point witnesses nonemptiness of the closed box, needed
-- when excluding a contradictory stable competitor.
theorem mixedWinner_W_of_strict_box (S : CompactStart) {mesh : ℕ}
    (rho : ℝ) (screen buffer delta : ℚ)
    (inherited : Code mesh → LabeledBranch 5)
    (argument : Fin 6 → Code mesh → SourceForm → ℚ)
    (code : Code mesh) (x : Fin 5 → ℝ)
    (hx : inBox (boxOfCode S (prefixCode 3 code)) x)
    (hW : WBoxCheck S (prefixCode 3 code) rho buffer delta)
    (hbase : 0 < gapLower (wRow S (prefixCode 3 code) buffer).cap
      (inherited (prefixCode 3 code)).cap
      (boxOfCode S (prefixCode 3 code)))
    (hrest : ∀ c ∈ mixedRows S rho screen buffer delta argument
      (prefixCode 3 code), c ≠ wRow S (prefixCode 3 code) buffer →
        0 < gapLower (wRow S (prefixCode 3 code) buffer).cap c.cap
          (boxOfCode S (prefixCode 3 code))) :
    mixedWinner S rho screen buffer delta inherited argument code =
      some (wRow S (prefixCode 3 code) buffer) := by
  let pc := prefixCode 3 code
  let wr := wRow S pc buffer
  let rows := mixedRows S rho screen buffer delta argument pc
  let box := boxOfCode S pc
  let base := inherited pc
  have hmem : wr ∈ rows := by
    apply List.mem_append.mpr
    right
    simp only [if_pos hW, List.mem_singleton]
  have hdom : dominates box base rows wr := by
    refine ⟨Or.inr hbase, ?_⟩
    intro c hc
    by_cases heq : c = wr
    · exact Or.inl (congrArg SelectedBranchData.cap heq.symm)
    · exact Or.inr (hrest c hc heq)
  have hnotbase : ¬ stableBase box base rows := by
    intro hb
    have hle := dominates_eval base.cap wr.cap box x hx (hb wr hmem)
    have hgap := gapLower_le_eval_gap wr.cap base.cap box x hx
    have hpos : (0 : ℝ) < gapLower wr.cap base.cap box := by
      exact_mod_cast hbase
    linarith
  have huniq : ∀ c ∈ rows, dominates box base rows c → c = wr := by
    intro c hc hdc
    by_contra hne
    have hgap := gapLower_le_eval_gap wr.cap c.cap box x hx
    have hpos : (0 : ℝ) < gapLower wr.cap c.cap box := by
      exact_mod_cast hrest c hc hne
    have hle := dominates_eval c.cap wr.cap box x hx (hdc.2 wr hmem)
    linarith
  have hfirst := firstStable_eq_of_unique hmem hdom huniq
  change (if stableBase box base rows then none else
    firstStable (dominates box base rows) rows) = some wr
  rw [if_neg hnotbase]
  exact hfirst

end
end ImbalancedChen.P2OriginalMixedThirdWTentSelector
