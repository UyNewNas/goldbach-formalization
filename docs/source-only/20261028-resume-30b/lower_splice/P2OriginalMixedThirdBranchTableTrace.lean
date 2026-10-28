import ImbalancedChen.P2OriginalMixedThirdWTentSelector
import ImbalancedChen.P2OriginalLowerWJointTraceSplice

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual finite optimizing mixed selector now supplies the rank-three
scalar row. A rejected or crossing cell inherits; successful tent/W rows
are compiled from their own affine whole-box cap and original argument.
The compiler still checks its exact incoming parent and square gates.
This is not a claim of complete chamber coverage or signed I3 closure.
-/
namespace ImbalancedChen.P2OriginalMixedThirdBranchTableTrace
noncomputable section
open scoped Classical BigOperators
open P2PhysicalIncomingPrefixCells P2LowerCapPlanIntegerRetention
open P2OriginalLowerSelectedCapConstructor (Code BranchTable prefixCode)
open P2OriginalLowerAffineTieSelector
open P2OriginalLowerBufferedAffineBoxes (wholeBoxInfimum lowerVertex)
open P2OriginalLowerCompactStartCapConstructor
open P2OriginalLowerNestedBufferedStages
open P2OriginalLowerWholeBoxBranchSelect
open P2OriginalLowerWThirdPhysicalRow
open P2OriginalMixedThirdWTentSelector

private theorem prefix3_idem {mesh : ℕ} (code : Code mesh) :
    prefixCode 3 (prefixCode 3 code) = prefixCode 3 code :=
  prefixCode_nested 3 3 (le_refl _) code

theorem mixedWinner_prefix3 (S : CompactStart) {mesh : ℕ} (rho : ℝ)
    (screen buffer delta : ℚ) (inherited : Code mesh → LabeledBranch 5)
    (argument : Fin 6 → Code mesh → SourceForm → ℚ) (code : Code mesh) :
    mixedWinner S rho screen buffer delta inherited argument (prefixCode 3 code) =
      mixedWinner S rho screen buffer delta inherited argument code := by
  simp only [mixedWinner, prefix3_idem]

/-- Only rank three is replaced. The selected source form remains available
from the same mixedWinner; it is never reconstructed from a scalar value. -/
def mixedThirdRows (S : CompactStart) {mesh : ℕ} (rows : BranchTable mesh)
    (rho : ℝ) (screen buffer delta : ℚ)
    (inherited : Code mesh → LabeledBranch 5)
    (argument : Fin 6 → Code mesh → SourceForm → ℚ) : BranchTable mesh :=
  ⟨fun rank code => if rank.val = 3 then
    (mixedWinner S rho screen buffer delta inherited argument code).map
      (fun b => (bufferedCap S (prefixCode 3 code) buffer b, b.argument))
    else rows.row rank code⟩

def mixedPlan (S : CompactStart) {mesh : ℕ} (rows : BranchTable mesh)
    (rho : ℝ) (screen buffer delta : ℚ)
    (inherited : Code mesh → LabeledBranch 5)
    (argument : Fin 6 → Code mesh → SourceForm → ℚ) : CapPlan 5 mesh :=
  compactPlan S (mixedThirdRows S rows rho screen buffer delta inherited argument) rho

/-- Both lower starts and the fourth/fifth finite stage data are retained.
Their checked parent is recomputed from this same merged table. -/
def mixedJointPlan (J : JointCompactStarts) {mesh : ℕ}
    (stages : JointStageData mesh) (rho : ℝ)
    (screen buffer3 buffer4 buffer5 delta : ℚ) (start : Fin 2)
    (inherited : Code mesh → LabeledBranch 5)
    (argument : Fin 6 → Code mesh → SourceForm → ℚ) : CapPlan 5 mesh :=
  mixedPlan (J.at start) (rowsForStart stages buffer3 buffer4 buffer5 start)
    rho screen buffer3 delta inherited argument

theorem mixedThirdRows_other_rank (S : CompactStart) {mesh : ℕ}
    (rows : BranchTable mesh) (rho : ℝ) (screen buffer delta : ℚ)
    (inherited : Code mesh → LabeledBranch 5)
    (argument : Fin 6 → Code mesh → SourceForm → ℚ)
    (rank : Fin 6) (code : Code mesh) (hr : rank.val ≠ 3) :
    (mixedThirdRows S rows rho screen buffer delta inherited argument).row rank code =
      rows.row rank code := by
  simp [mixedThirdRows, hr]

theorem mixedThirdRows_selected (S : CompactStart) {mesh : ℕ}
    (rows : BranchTable mesh) (rho : ℝ) (screen buffer delta : ℚ)
    (inherited : Code mesh → LabeledBranch 5)
    (argument : Fin 6 → Code mesh → SourceForm → ℚ)
    (code : Code mesh) (b : SelectedBranchData)
    (hsel : mixedWinner S rho screen buffer delta inherited argument code = some b) :
    (mixedThirdRows S rows rho screen buffer delta inherited argument).row 3
      (prefixCode 3 code) =
      some (bufferedCap S (prefixCode 3 code) buffer b, b.argument) := by
  simp [mixedThirdRows, mixedWinner_prefix3, prefix3_idem, hsel]

/-- The W row uses exactly the same affine lower vertex and buffer as its
independent physical licence. There is no second buffer subtraction. -/
theorem bufferedCap_wRow (S : CompactStart) {mesh : ℕ}
    (code : Code mesh) (buffer : ℚ) :
    bufferedCap S code buffer (wRow S code buffer) = wCap S code buffer := by
  norm_num [bufferedCap, wRow, SelectedBranchData.cap, SourceForm.affine,
    wholeBoxInfimum, lowerVertex, Fin.sum_univ_succ,
    P2OriginalLowerCompactStartCapConstructor.boxOfCode, qHi, wCap] <;> ring

/-- Checked compilation computes the exact mixed selected action. Geometry
failure keeps inherit, rather than introducing a replacement hypothesis. -/
theorem mixed_checkedChoice (S : CompactStart) {mesh : ℕ}
    (rows : BranchTable mesh) (rho : ℝ) (screen buffer delta : ℚ)
    (inherited : Code mesh → LabeledBranch 5)
    (argument : Fin 6 → Code mesh → SourceForm → ℚ)
    (code : Code mesh) (b : SelectedBranchData)
    (hsel : mixedWinner S rho screen buffer delta inherited argument code = some b) :
    checkedChoice S
      (mixedThirdRows S rows rho screen buffer delta inherited argument) 3
      (baselineCap rho) code =
      if branchGates S 3 (baselineCap rho)
          (bufferedCap S (prefixCode 3 code) buffer b : ℝ) (prefixCode 3 code)
      then .fresh (bufferedCap S (prefixCode 3 code) buffer b) b.argument
      else .inherit 2 := by
  unfold checkedChoice
  rw [mixedThirdRows_selected S rows rho screen buffer delta inherited argument
    code b hsel]

/-- The same selected source label retains its actual-buffer licence.
Tent and W provenance stay disjoint; W is never assigned a tent mask. -/
theorem mixed_selected_actual_licence (S : CompactStart) {mesh : ℕ}
    (rho : ℝ) (screen buffer delta : ℚ)
    (inherited : Code mesh → LabeledBranch 5)
    (argument : Fin 6 → Code mesh → SourceForm → ℚ)
    (code : Code mesh) (b : SelectedBranchData) (hbuffer : buffer ≤ screen)
    (hsel : mixedWinner S rho screen buffer delta inherited argument code = some b) :
    supportCheck S 3 (prefixCode 3 code) buffer b ∨
      (b = wRow S (prefixCode 3 code) buffer ∧
        WBoxCheck S (prefixCode 3 code) rho buffer delta) := by
  rcases mixedWinner_source S rho screen buffer delta inherited argument code b hsel
    with ht | hW
  · obtain ⟨_, _, _, hs⟩ := ht
    exact Or.inl (P2OriginalCompositeTentSelector.supportCheck_buffer_mono
      S 3 (prefixCode 3 code) screen buffer b hbuffer hs)
  · exact Or.inr hW

/-- A W winner extracts its independent WBoxCheck from the actual selector;
no additional final-plan or gate predicate is assumed. -/
theorem mixed_W_checkedChoice (S : CompactStart) {mesh : ℕ}
    (rows : BranchTable mesh) (rho : ℝ) (screen buffer delta : ℚ)
    (inherited : Code mesh → LabeledBranch 5)
    (argument : Fin 6 → Code mesh → SourceForm → ℚ) (code : Code mesh)
    (hsel : mixedWinner S rho screen buffer delta inherited argument code =
      some (wRow S (prefixCode 3 code) buffer)) :
    checkedChoice S
      (mixedThirdRows S rows rho screen buffer delta inherited argument) 3
      (baselineCap rho) code =
      .fresh (wCap S (prefixCode 3 code) buffer)
        (wQueryLower S (prefixCode 3 code) buffer) := by
  have hW := (mixedWinner_W_physical_row S rho screen buffer delta
    inherited argument code hsel).1
  rw [mixed_checkedChoice S rows rho screen buffer delta inherited argument
    code _ hsel, bufferedCap_wRow]
  simp only [hW.compact_gates, if_true, wRow]

private theorem rank3_trace_cap_of_choice {mesh : ℕ} (P : CapPlan 5 mesh)
    (a w seed c query : ℝ) (N p1 p2 p3 : ℕ) (code : Code mesh)
    (hcode : incomingCode a w 5 mesh 3
      (marked (physicalWord N [p3,p2,p1])) = code)
    (hchoice : P.choose 3 code = .fresh c query) :
    (integerTrace P a w seed N [p3,p2,p1]).cap = c := by
  let before := integerTrace P a w seed N [p2,p1]
  have hword : before.word ++ [coordinate N p3] =
      physicalWord N [p3,p2,p1] := by
    rw [integerTrace_word]
    simp [physicalWord]
  have hc : planChoice P a w (physicalWord N [p3,p2,p1]) = .fresh c query := by
    have hlen : (physicalWord N [p3,p2,p1]).length = 3 := by simp [physicalWord]
    simp only [planChoice, hlen, eq_self, true_or, if_true]
    unfold incomingChoice
    simp only [Nat.min_eq_left (by omega : 3 ≤ 5)]
    rw [hcode]
    exact hchoice
  rw [integerTrace_cons]
  change (planChoice P a w (before.word ++ [coordinate N p3])).freeze before.cap = c
  rw [hword, hc]
  rfl

/-- Every accepted mixed tent or W row has the same source cap and query
in the actual Trace. Only strict physical branch geometry is an input. -/
theorem mixed_selected_actual_third_trace (S : CompactStart) {mesh : ℕ}
    (rows : BranchTable mesh) (rho : ℝ) (screen buffer delta : ℚ)
    (inherited : Code mesh → LabeledBranch 5)
    (argument : Fin 6 → Code mesh → SourceForm → ℚ)
    (N p1 p2 p3 : ℕ) (code : Code mesh) (b : SelectedBranchData)
    (hcode : incomingCode (S.epsilon : ℝ) (startCutoff S.start : ℝ)
      5 mesh 3 (marked (physicalWord N [p3,p2,p1])) = code)
    (hsel : mixedWinner S rho screen buffer delta inherited argument code = some b)
    (hg : branchGates S 3 (baselineCap rho)
      (bufferedCap S (prefixCode 3 code) buffer b : ℝ) (prefixCode 3 code)) :
    (integerTrace (mixedPlan S rows rho screen buffer delta inherited argument)
      (S.epsilon : ℝ) (startCutoff S.start : ℝ) (baselineCap rho)
      N [p3,p2,p1]).cap = (bufferedCap S (prefixCode 3 code) buffer b : ℝ) := by
  apply rank3_trace_cap_of_choice _ _ _ _ _ b.argument N p1 p2 p3 code hcode
  change checkedChoice S _ 3 (baselineCap rho) code = _
  rw [mixed_checkedChoice S rows rho screen buffer delta inherited argument code b hsel]
  simp only [hg, if_true]

/-- This freezes the optimizing mixed selector's actual W winner in the
computed physical Trace, rather than the earlier unconditional W priority. -/
theorem mixed_W_actual_third_trace (S : CompactStart) {mesh : ℕ}
    (rows : BranchTable mesh) (rho : ℝ) (screen buffer delta : ℚ)
    (inherited : Code mesh → LabeledBranch 5)
    (argument : Fin 6 → Code mesh → SourceForm → ℚ)
    (N p1 p2 p3 : ℕ) (code : Code mesh)
    (hcode : incomingCode (S.epsilon : ℝ) (startCutoff S.start : ℝ)
      5 mesh 3 (marked (physicalWord N [p3,p2,p1])) = code)
    (hsel : mixedWinner S rho screen buffer delta inherited argument code =
      some (wRow S (prefixCode 3 code) buffer)) :
    (integerTrace (mixedPlan S rows rho screen buffer delta inherited argument)
      (S.epsilon : ℝ) (startCutoff S.start : ℝ) (baselineCap rho)
      N [p3,p2,p1]).cap = (wCap S (prefixCode 3 code) buffer : ℝ) := by
  apply rank3_trace_cap_of_choice _ _ _ _ _ _ N p1 p2 p3 code hcode
  change checkedChoice S _ 3 (baselineCap rho) code = _
  exact mixed_W_checkedChoice S rows rho screen buffer delta inherited argument code hsel

/-- Fourth action's parent is the same optimizing mixed W cap. Its stored
row survives, while branchGates are rechecked against this parent. -/
theorem mixed_W_fourth_choice (S : CompactStart) {mesh : ℕ}
    (rows : BranchTable mesh) (rho : ℝ) (screen buffer delta : ℚ)
    (inherited : Code mesh → LabeledBranch 5)
    (argument : Fin 6 → Code mesh → SourceForm → ℚ) (code : Code mesh)
    (hsel : mixedWinner S rho screen buffer delta inherited argument code =
      some (wRow S (prefixCode 3 code) buffer)) :
    (mixedPlan S rows rho screen buffer delta inherited argument).choose 4 code =
      checkedChoice S (mixedThirdRows S rows rho screen buffer delta inherited argument)
        4 (wCap S (prefixCode 3 code) buffer : ℝ) code := by
  have hc : cap3 S (mixedThirdRows S rows rho screen buffer delta inherited argument)
      rho code = (wCap S (prefixCode 3 code) buffer : ℝ) := by
    unfold cap3 checkedCap
    rw [mixed_W_checkedChoice S rows rho screen buffer delta inherited argument code hsel]
    rfl
  change checkedChoice S _ 4 (cap3 _ _ rho code) code = _
  rw [hc]

/-- The reached frontier retains both seed-level tests; only the new fourth
cube reads the selected W cap. -/
theorem mixed_W_fourth_retention (S : CompactStart) {mesh : ℕ}
    (rows : BranchTable mesh) (rho : ℝ) (screen buffer delta : ℚ)
    (inherited : Code mesh → LabeledBranch 5)
    (argument : Fin 6 → Code mesh → SourceForm → ℚ)
    (N p1 p2 p3 p4 : ℕ) (code : Code mesh)
    (hcode : incomingCode (S.epsilon : ℝ) (startCutoff S.start : ℝ)
      5 mesh 3 (marked (physicalWord N [p3,p2,p1])) = code)
    (hsel : mixedWinner S rho screen buffer delta inherited argument code =
      some (wRow S (prefixCode 3 code) buffer)) :
    retainEven (mixedPlan S rows rho screen buffer delta inherited argument)
      (S.epsilon : ℝ) (startCutoff S.start : ℝ) (baselineCap rho)
      N [p4,p3,p2,p1] = true ↔
      (2 * coordinate N p1 < baselineCap rho ∧
        coordinate N p1 + 3 * coordinate N p2 < baselineCap rho) ∧
      (physicalWord N [p3,p2,p1]).sum + 3 * coordinate N p4 <
        (wCap S (prefixCode 3 code) buffer : ℝ) := by
  rw [retainEven_cons_iff]
  rw [even_rank_cube _ _ _ _ N p4 [p3,p2,p1] (by simp) (by norm_num)]
  rw [mixed_W_actual_third_trace S rows rho screen buffer delta inherited argument
    N p1 p2 p3 code hcode hsel]
  rw [odd_rank_bypass _ _ _ _ N p3 [p2,p1] (by simp) (by norm_num)]
  rw [P2OriginalLowerWJointTraceSplice.baseline_two_tests]

end
end ImbalancedChen.P2OriginalMixedThirdBranchTableTrace
