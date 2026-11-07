import ImbalancedChen.P2OriginalLowerFiniteAffineMeshWidth
import ImbalancedChen.P2OriginalLowerWholeBoxBranchSelect

-- SOURCE ONLY / UNCOMPILED_ZERO_CREDIT.
-- Build a finite StageSpec from labelled affine chamber data, rather than
-- assuming a StageSpec supplier. The selected support-mask licence is a
-- primitive local gate boundary; the W_j factorization licence is distinct.
-- Gate-crossing cells need their own proper-wall mass treatment.

namespace ImbalancedChen.P2OriginalLowerLicensedChamberStage

noncomputable section
open scoped Classical
open P2PhysicalIncomingPrefixCells
open P2OriginalLowerSelectedCapConstructor
open P2OriginalLowerCompactStartCapConstructor
open P2OriginalLowerNestedBufferedStages
open P2OriginalLowerBufferedAffineBoxes
open P2OriginalLowerWholeBoxBranchSelect
open P2EnhancedLowerPhysicalNode

abbrev Cell (mesh : ℕ) := Fin 2 × Code mesh

-- This is the exact remaining primitive licence interface on a retained
-- compact chamber. It carries a selected source form and its mask, not a
-- final policy, density bound, or certificate of the eleven-root sum.
structure LicensedChamberBank (J : JointCompactStarts)
    (mesh : ℕ) (rank : Fin 6) where
  chosen : Cell mesh → Option SelectedBranchData
  retained : Cell mesh → Prop
  history : Cell mesh → Prop
  parent : Cell mesh → ℚ
  supportGate : Cell mesh → ℚ
  form_eligible : ∀ cell b, chosen cell = some b →
    formRankEligible rank b.form
  side_licensed : ∀ cell b, chosen cell = some b →
    sideCheck b
      (boxOfCode (J.at cell.1) (prefixCode rank.val cell.2))
  history_sufficient : ∀ cell, history cell →
    historicalGate (J.at cell.1) rank (parent cell : ℝ)
      (prefixCode rank.val cell.2)
  mask_gate_sound : ∀ cell b (cap : ℚ),
    chosen cell = some b → supportGate cell < cap →
      strictSquareGates (cap : ℝ) 0
        ((ownPrefixSlots (J.at cell.1) rank
          (prefixCode rank.val cell.2)
          b.form.supportMask).map Slot.exponent) ∧
      strictSquareGates (cap : ℝ)
        (selectedWord (ownPrefixSlots (J.at cell.1) rank
          (prefixCode rank.val cell.2)
          b.form.supportMask)).sum
        (remainingWord (ownPrefixSlots (J.at cell.1) rank
          (prefixCode rank.val cell.2)
          b.form.supportMask))

def endpoint {J : JointCompactStarts} {mesh : ℕ}
    {rank : Fin 6} (B : LicensedChamberBank J mesh rank)
    (cell : Cell mesh) : ℚ :=
  match B.chosen cell with
  | none => 0
  | some b => wholeBoxInfimum b.cap.constant b.cap.slope
      (boxOfCode (J.at cell.1) (prefixCode rank.val cell.2))

def argument {J : JointCompactStarts} {mesh : ℕ}
    {rank : Fin 6} (B : LicensedChamberBank J mesh rank)
    (cell : Cell mesh) : ℚ :=
  match B.chosen cell with
  | none => 2
  | some b => b.argument

def gate {J : JointCompactStarts} {mesh : ℕ}
    {rank : Fin 6} (B : LicensedChamberBank J mesh rank)
    (cell : Cell mesh) : ℚ :=
  max (B.parent cell) (B.supportGate cell)

-- A cell is active only if its labelled source is present, its own-rank
-- trimmed chamber and historical gate survive, and its whole-box affine
-- endpoint remains strictly above the parent/mask support gate.
def active {J : JointCompactStarts} {mesh : ℕ}
    {rank : Fin 6} (B : LicensedChamberBank J mesh rank) :
    Finset (Cell mesh) :=
  Finset.univ.filter (fun cell =>
    cell.2 = prefixCode rank.val cell.2 ∧
      B.retained cell ∧ B.history cell ∧
      ∃ b, B.chosen cell = some b ∧
        gate B cell < endpoint B cell)

theorem active_has_source {J : JointCompactStarts} {mesh : ℕ}
    {rank : Fin 6} (B : LicensedChamberBank J mesh rank)
    {cell : Cell mesh} (hcell : cell ∈ active B) :
    ∃ b, B.chosen cell = some b ∧
      cell.2 = prefixCode rank.val cell.2 ∧
      B.retained cell ∧ B.history cell ∧
      gate B cell < endpoint B cell := by
  obtain ⟨_,⟨hcanon,hret,hhist,b,hb,hgap⟩⟩ :=
    Finset.mem_filter.mp hcell
  exact ⟨b,hb,hcanon,hret,hhist,hgap⟩

def stage {J : JointCompactStarts} {mesh : ℕ}
    {rank : Fin 6} (B : LicensedChamberBank J mesh rank) :
    StageSpec mesh rank :=
  { active := active B
    parent := B.parent
    gate := gate B
    endpoint := endpoint B
    argument := argument B
    parent_le_gate := by
      intro cell _
      exact le_max_left _ _
    strict_gap := by
      intro cell hcell
      obtain ⟨_,_,_,_,_,hgap⟩ := active_has_source B hcell
      exact hgap }

theorem active_original_history {J : JointCompactStarts}
    {mesh : ℕ} {rank : Fin 6}
    (B : LicensedChamberBank J mesh rank)
    {cell : Cell mesh} (hcell : cell ∈ active B) :
    historicalGate (J.at cell.1) rank (B.parent cell : ℝ)
      (prefixCode rank.val cell.2) := by
  obtain ⟨_,_,_,_,hhist,_⟩ := active_has_source B hcell
  exact B.history_sufficient cell hhist

theorem active_source_licensed {J : JointCompactStarts}
    {mesh : ℕ} {rank : Fin 6}
    (B : LicensedChamberBank J mesh rank)
    {cell : Cell mesh} (hcell : cell ∈ active B) :
    ∃ b, B.chosen cell = some b ∧
      formRankEligible rank b.form ∧
      sideCheck b
        (boxOfCode (J.at cell.1)
          (prefixCode rank.val cell.2)) := by
  obtain ⟨b,hb,_,_,_,_⟩ := active_has_source B hcell
  exact ⟨b,hb,B.form_eligible cell b hb,
    B.side_licensed cell b hb⟩

structure BufferedStage {J : JointCompactStarts} {mesh : ℕ}
    {rank : Fin 6} (B : LicensedChamberBank J mesh rank)
    (eta : ℚ) where
  buffer : ℚ
  buffer_pos : 0 < buffer
  buffer_lt_eta : buffer < eta
  gap : ∀ cell ∈ (stage B).active,
    (stage B).parent cell < (stage B).endpoint cell - buffer ∧
    (stage B).gate cell < (stage B).endpoint cell - buffer ∧
    (stage B).endpoint cell - buffer < (stage B).endpoint cell

theorem exists_buffered_stage {J : JointCompactStarts} {mesh : ℕ}
    {rank : Fin 6} (B : LicensedChamberBank J mesh rank)
    (eta : ℚ) (heta : 0 < eta) :
    Nonempty (BufferedStage B eta) := by
  obtain ⟨buffer,hb,hbe,hgap⟩ :=
    exists_stage_buffer (stage B) eta heta
  exact ⟨⟨buffer,hb,hbe,hgap⟩⟩

theorem buffered_stage_row_at_active_cell {J : JointCompactStarts}
    {mesh : ℕ} {rank : Fin 6}
    (B : LicensedChamberBank J mesh rank) {eta : ℚ}
    (F : BufferedStage B eta) {cell : Cell mesh}
    (hcell : cell ∈ (stage B).active) :
    stageRow (stage B) F.buffer cell.1 cell.2 =
      some ((stage B).endpoint cell - F.buffer,
        (stage B).argument cell) := by
  obtain ⟨_,_,hcanon,_,_,_⟩ := active_has_source B hcell
  simp [stageRow, hcanon, hcell]

-- Keep the actual per-cell gap witness obtained from the finite buffer.
-- It yields masked full and selected-remaining square gates for each
-- active candidate, rather than being discarded after table construction.
theorem buffered_active_mask_gates {J : JointCompactStarts}
    {mesh : ℕ} {rank : Fin 6}
    (B : LicensedChamberBank J mesh rank) {eta : ℚ}
    (F : BufferedStage B eta) {cell : Cell mesh}
    (hcell : cell ∈ (stage B).active) :
    ∃ b, B.chosen cell = some b ∧
      strictSquareGates
        (((stage B).endpoint cell - F.buffer : ℚ) : ℝ) 0
        ((ownPrefixSlots (J.at cell.1) rank
          (prefixCode rank.val cell.2)
          b.form.supportMask).map Slot.exponent) ∧
      strictSquareGates
        (((stage B).endpoint cell - F.buffer : ℚ) : ℝ)
        (selectedWord (ownPrefixSlots (J.at cell.1) rank
          (prefixCode rank.val cell.2)
          b.form.supportMask)).sum
        (remainingWord (ownPrefixSlots (J.at cell.1) rank
          (prefixCode rank.val cell.2)
          b.form.supportMask)) := by
  obtain ⟨b,hb,_,_,_,_⟩ := active_has_source B hcell
  have hgap := (F.gap cell hcell).2.1
  have hsupport : B.supportGate cell <
      (stage B).endpoint cell - F.buffer :=
    lt_of_le_of_lt (le_max_right _ _) hgap
  obtain ⟨hfull,hselected⟩ := B.mask_gate_sound cell b
    ((stage B).endpoint cell - F.buffer) hb hsupport
  exact ⟨b,hb,hfull,hselected⟩

-- Every point of the full compact cube has a finite corrected code box.
-- Whether it lies in the retained chamber subset is a separate proper-wall
-- trimming statement; failure of a whole-box gate is not physical rejection.
def codeOfPoint (S : CompactStart) (mesh : ℕ)
    (marks : Fin 5 → Bool) (x : Fin 5 → ℝ) : Code mesh :=
  fun i => (exponentCode (S.epsilon : ℝ)
    (startCutoff S.start : ℝ) mesh (x i), marks i)

theorem compact_code_cover (S : CompactStart) (mesh : ℕ)
    (marks : Fin 5 → Bool) (x : Fin 5 → ℝ)
    (hx : ∀ i, x i ∈ Set.Icc (S.epsilon : ℝ)
      (startCutoff S.start : ℝ)) :
    inBox (boxOfCode S (codeOfPoint S mesh marks x)) x := by
  apply inBox_of_exponentCodes
  intro i
  exact exponentCode_membership (hx i)

end
end ImbalancedChen.P2OriginalLowerLicensedChamberStage
