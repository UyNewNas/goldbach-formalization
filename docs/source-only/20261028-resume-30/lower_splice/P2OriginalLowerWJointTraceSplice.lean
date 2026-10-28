import ImbalancedChen.P2OriginalLowerNestedBufferedStages
import ImbalancedChen.P2OriginalLowerWThirdPhysicalRow
import ImbalancedChen.P2LowerCapPlanIntegerRetention

/-!
Source-only candidate. No compilation or formal acceptance is asserted.

An explicit W-priority merge, followed by the existing checked causal
compiler. Rank four and rank five rows are retained, but their branch tests
read the caps produced by the merged preceding stages. The third W row is
proved from the merge definition, rather than supplied as a row-identity
hypothesis. This construction is a licensed alternative, not a claim that
it is the optimizing selected bank or that its integral meets a target.
-/
namespace ImbalancedChen.P2OriginalLowerWJointTraceSplice

noncomputable section
open scoped Classical
open P2PhysicalIncomingPrefixCells
open P2LowerCapPlanIntegerRetention
open P2OriginalLowerSelectedCapConstructor (Code BranchTable prefixCode)
open P2OriginalLowerCompactStartCapConstructor
open P2OriginalLowerNestedBufferedStages
open P2OriginalLowerWThirdPhysicalRow

/-- W wins the explicitly declared priority only on its checked whole box.
All other rank-three rows and every later row keep their previous data. -/
def WPriorityRows (S : CompactStart) {mesh : ℕ}
    (rows : BranchTable mesh) (rho : ℝ) (buffer delta : ℚ) :
    BranchTable mesh :=
  ⟨fun rank code =>
    if rank.val = 3 then
      if WBoxCheck S code rho buffer delta then
        some (wCap S code buffer, wQueryLower S code buffer)
      else rows.row rank code
    else rows.row rank code⟩

def WPriorityPlan (J : JointCompactStarts) {mesh : ℕ}
    (stages : JointStageData mesh) (buffer3 buffer4 buffer5 delta : ℚ)
    (rho : ℝ) (start : Fin 2) : CapPlan 5 mesh :=
  compactPlan (J.at start)
    (WPriorityRows (J.at start)
      (rowsForStart stages buffer3 buffer4 buffer5 start)
      rho buffer3 delta) rho

theorem WPriorityRows_third (S : CompactStart) {mesh : ℕ}
    (rows : BranchTable mesh) (rho : ℝ) (buffer delta : ℚ)
    (code : Code mesh) (hW : WBoxCheck S code rho buffer delta) :
    (WPriorityRows S rows rho buffer delta).row 3 code =
      some (wCap S code buffer, wQueryLower S code buffer) := by
  simp [WPriorityRows, hW]

theorem WPriorityRows_nonW (S : CompactStart) {mesh : ℕ}
    (rows : BranchTable mesh) (rho : ℝ) (buffer delta : ℚ)
    (code : Code mesh) (hW : ¬ WBoxCheck S code rho buffer delta) :
    (WPriorityRows S rows rho buffer delta).row 3 code = rows.row 3 code := by
  simp [WPriorityRows, hW]

theorem WPriorityRows_other_rank (S : CompactStart) {mesh : ℕ}
    (rows : BranchTable mesh) (rho : ℝ) (buffer delta : ℚ)
    (rank : Fin 6) (code : Code mesh) (hr : rank.val ≠ 3) :
    (WPriorityRows S rows rho buffer delta).row rank code =
      rows.row rank code := by
  simp [WPriorityRows, hr]

/-- The merged third-row value is computed, not assumed. -/
theorem WPriorityRows_checked_third (S : CompactStart) {mesh : ℕ}
    (rows : BranchTable mesh) (rho : ℝ) (buffer delta : ℚ)
    (code : Code mesh)
    (hW : WBoxCheck S (prefixCode 3 code) rho buffer delta) :
    checkedChoice S (WPriorityRows S rows rho buffer delta) 3
      (baselineCap rho) code =
      .fresh (wCap S (prefixCode 3 code) buffer)
        (wQueryLower S (prefixCode 3 code) buffer) := by
  unfold checkedChoice
  rw [WPriorityRows_third S rows rho buffer delta (prefixCode 3 code) hW]
  simp [hW.compact_gates]

theorem WPriorityRows_cap3 (S : CompactStart) {mesh : ℕ}
    (rows : BranchTable mesh) (rho : ℝ) (buffer delta : ℚ)
    (code : Code mesh)
    (hW : WBoxCheck S (prefixCode 3 code) rho buffer delta) :
    cap3 S (WPriorityRows S rows rho buffer delta) rho code =
      (wCap S (prefixCode 3 code) buffer : ℝ) := by
  unfold cap3 checkedCap
  rw [WPriorityRows_checked_third S rows rho buffer delta code hW]
  rfl

/-- Fourth-stage tests use the actual frozen W cap. The old fourth row is
kept, but no test against the ideal/unmerged parent is reused. -/
theorem WPriorityPlan_fourth_choice (J : JointCompactStarts) {mesh : ℕ}
    (stages : JointStageData mesh) (buffer3 buffer4 buffer5 delta : ℚ)
    (rho : ℝ) (start : Fin 2) (code : Code mesh)
    (hW : WBoxCheck (J.at start) (prefixCode 3 code) rho buffer3 delta) :
    (WPriorityPlan J stages buffer3 buffer4 buffer5 delta rho start).choose
      4 code =
    checkedChoice (J.at start)
      (WPriorityRows (J.at start)
        (rowsForStart stages buffer3 buffer4 buffer5 start)
        rho buffer3 delta) 4
      (wCap (J.at start) (prefixCode 3 code) buffer3 : ℝ) code := by
  change checkedChoice _ _ 4 (cap3 _ _ rho code) code = _
  rw [WPriorityRows_cap3 _ _ rho buffer3 delta code hW]

/-- The computed rank-three Trace is the same physical prefix lookup as
in the joint rows, with the same start and third-stage buffer. -/
theorem WPriorityPlan_third_trace_cap (J : JointCompactStarts) {mesh : ℕ}
    (stages : JointStageData mesh) (buffer3 buffer4 buffer5 delta : ℚ)
    (rho : ℝ) (start : Fin 2) (N p1 p2 p3 : ℕ) (code : Code mesh)
    (hcode : incomingCode (J.epsilon : ℝ)
      (startCutoff (J.at start).start : ℝ) 5 mesh 3
      (marked (physicalWord N [p3,p2,p1])) = code)
    (hW : WBoxCheck (J.at start) (prefixCode 3 code) rho buffer3 delta) :
    (integerTrace
      (WPriorityPlan J stages buffer3 buffer4 buffer5 delta rho start)
      (J.epsilon : ℝ) (startCutoff (J.at start).start : ℝ)
      (baselineCap rho) N [p3,p2,p1]).cap =
      (wCap (J.at start) (prefixCode 3 code) buffer3 : ℝ) := by
  let P := WPriorityPlan J stages buffer3 buffer4 buffer5 delta rho start
  let before := integerTrace P (J.epsilon : ℝ)
    (startCutoff (J.at start).start : ℝ) (baselineCap rho) N [p2,p1]
  have hword : before.word ++ [coordinate N p3] =
      physicalWord N [p3,p2,p1] := by
    rw [integerTrace_word]
    simp [physicalWord]
  have hchoice : planChoice P (J.epsilon : ℝ)
      (startCutoff (J.at start).start : ℝ)
      (physicalWord N [p3,p2,p1]) =
      .fresh (wCap (J.at start) (prefixCode 3 code) buffer3)
        (wQueryLower (J.at start) (prefixCode 3 code) buffer3) := by
    have hlen : (physicalWord N [p3,p2,p1]).length = 3 := by
      simp [physicalWord]
    simp only [planChoice, hlen, eq_self, true_or, if_true]
    unfold incomingChoice
    simp only [Nat.min_eq_left (by omega : 3 ≤ 5)]
    rw [hcode]
    change checkedChoice (J.at start) _ 3 (baselineCap rho) code = _
    exact WPriorityRows_checked_third _ _ rho buffer3 delta code hW
  rw [integerTrace_cons]
  change (planChoice P (J.epsilon : ℝ)
    (startCutoff (J.at start).start : ℝ)
    (before.word ++ [coordinate N p3])).freeze before.cap = _
  rw [hword, hchoice]
  rfl

/-- No cap action occurs at ranks one or two. These two old tests are
therefore exactly the original seed-level square and second cube. -/
theorem baseline_two_tests {depth mesh : ℕ} (P : CapPlan depth mesh)
    (a b seed : ℝ) (N p1 p2 : ℕ) :
    retainEven P a b seed N [p2,p1] = true ↔
      2 * coordinate N p1 < seed ∧
        coordinate N p1 + 3 * coordinate N p2 < seed := by
  simp [retainEven, integerTrace, physicalWord, run, root, step,
    planChoice, admission, CapChoice.freeze, Bool.and_eq_true,
    decide_eq_true_eq]

/-- An odd third rank retains exactly its earlier first/second tests.
A new W cap cannot retroactively replace their incoming baseline cap. -/
theorem WPriorityPlan_third_retention (J : JointCompactStarts) {mesh : ℕ}
    (stages : JointStageData mesh) (buffer3 buffer4 buffer5 delta : ℚ)
    (rho : ℝ) (start : Fin 2) (N p1 p2 p3 : ℕ) :
    retainEven (WPriorityPlan J stages buffer3 buffer4 buffer5 delta rho start)
      (J.epsilon : ℝ) (startCutoff (J.at start).start : ℝ)
      (baselineCap rho) N [p3,p2,p1] = true ↔
    retainEven (WPriorityPlan J stages buffer3 buffer4 buffer5 delta rho start)
      (J.epsilon : ℝ) (startCutoff (J.at start).start : ℝ)
      (baselineCap rho) N [p2,p1] = true := by
  exact odd_rank_bypass _ _ _ _ N p3 [p2,p1] (by simp) (by norm_num)

/-- The reached fourth frontier has the inherited tests AND its new cube
at the actual frozen W cap. This is a restricted-history identity, not a
global equality with a constant-new-cap Rosser policy. -/
theorem WPriorityPlan_fourth_retention (J : JointCompactStarts) {mesh : ℕ}
    (stages : JointStageData mesh) (buffer3 buffer4 buffer5 delta : ℚ)
    (rho : ℝ) (start : Fin 2) (N p1 p2 p3 p4 : ℕ) (code : Code mesh)
    (hcode : incomingCode (J.epsilon : ℝ)
      (startCutoff (J.at start).start : ℝ) 5 mesh 3
      (marked (physicalWord N [p3,p2,p1])) = code)
    (hW : WBoxCheck (J.at start) (prefixCode 3 code) rho buffer3 delta) :
    retainEven (WPriorityPlan J stages buffer3 buffer4 buffer5 delta rho start)
      (J.epsilon : ℝ) (startCutoff (J.at start).start : ℝ)
      (baselineCap rho) N [p4,p3,p2,p1] = true ↔
      retainEven (WPriorityPlan J stages buffer3 buffer4 buffer5 delta rho start)
        (J.epsilon : ℝ) (startCutoff (J.at start).start : ℝ)
        (baselineCap rho) N [p2,p1] = true ∧
      (physicalWord N [p3,p2,p1]).sum + 3 * coordinate N p4 <
        (wCap (J.at start) (prefixCode 3 code) buffer3 : ℝ) := by
  rw [retainEven_cons_iff]
  rw [even_rank_cube _ _ _ _ N p4 [p3,p2,p1] (by simp) (by norm_num)]
  rw [WPriorityPlan_third_trace_cap J stages buffer3 buffer4 buffer5 delta
    rho start N p1 p2 p3 code hcode hW]
  rw [WPriorityPlan_third_retention]

/-- The complete reached fourth-prefix condition displays both inherited
seed-level gates separately from the new cube at the W level. -/
theorem WPriorityPlan_fourth_full_physical_gates
    (J : JointCompactStarts) {mesh : ℕ}
    (stages : JointStageData mesh) (buffer3 buffer4 buffer5 delta : ℚ)
    (rho : ℝ) (start : Fin 2) (N p1 p2 p3 p4 : ℕ) (code : Code mesh)
    (hcode : incomingCode (J.epsilon : ℝ)
      (startCutoff (J.at start).start : ℝ) 5 mesh 3
      (marked (physicalWord N [p3,p2,p1])) = code)
    (hW : WBoxCheck (J.at start) (prefixCode 3 code) rho buffer3 delta) :
    retainEven (WPriorityPlan J stages buffer3 buffer4 buffer5 delta rho start)
      (J.epsilon : ℝ) (startCutoff (J.at start).start : ℝ)
      (baselineCap rho) N [p4,p3,p2,p1] = true ↔
      (2 * coordinate N p1 < baselineCap rho ∧
        coordinate N p1 + 3 * coordinate N p2 < baselineCap rho) ∧
      (physicalWord N [p3,p2,p1]).sum + 3 * coordinate N p4 <
        (wCap (J.at start) (prefixCode 3 code) buffer3 : ℝ) := by
  rw [WPriorityPlan_fourth_retention J stages buffer3 buffer4 buffer5 delta
    rho start N p1 p2 p3 p4 code hcode hW]
  rw [baseline_two_tests]

/-- The same reached-frontier test in the natural integer multiplier.
The old first/second tests are still retained verbatim on the left factor. -/
theorem WPriorityPlan_fourth_integer_gate (J : JointCompactStarts) {mesh : ℕ}
    (stages : JointStageData mesh) (buffer3 buffer4 buffer5 delta : ℚ)
    (rho : ℝ) (start : Fin 2) (N p1 p2 p3 p4 : ℕ) (code : Code mesh)
    (hN : 1 < (N : ℝ)) (hp1 : 0 < p1) (hp2 : 0 < p2)
    (hp3 : 0 < p3) (hp4 : 0 < p4)
    (hcode : incomingCode (J.epsilon : ℝ)
      (startCutoff (J.at start).start : ℝ) 5 mesh 3
      (marked (physicalWord N [p3,p2,p1])) = code)
    (hW : WBoxCheck (J.at start) (prefixCode 3 code) rho buffer3 delta) :
    retainEven (WPriorityPlan J stages buffer3 buffer4 buffer5 delta rho start)
      (J.epsilon : ℝ) (startCutoff (J.at start).start : ℝ)
      (baselineCap rho) N [p4,p3,p2,p1] = true ↔
      retainEven (WPriorityPlan J stages buffer3 buffer4 buffer5 delta rho start)
        (J.epsilon : ℝ) (startCutoff (J.at start).start : ℝ)
        (baselineCap rho) N [p2,p1] = true ∧
      ([p3,p2,p1].prod : ℝ) * (p4 : ℝ)^3 <
        (N : ℝ) ^ (wCap (J.at start) (prefixCode 3 code) buffer3 : ℝ) := by
  rw [WPriorityPlan_fourth_retention J stages buffer3 buffer4 buffer5 delta
    rho start N p1 p2 p3 p4 code hcode hW]
  rw [cube_test_integer_iff hN hp4 [p3,p2,p1]
    (by intro q hq; simp only [List.mem_cons, List.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl
        · exact hp3
        · exact hp2
        · exact hp1)]

end
end ImbalancedChen.P2OriginalLowerWJointTraceSplice
