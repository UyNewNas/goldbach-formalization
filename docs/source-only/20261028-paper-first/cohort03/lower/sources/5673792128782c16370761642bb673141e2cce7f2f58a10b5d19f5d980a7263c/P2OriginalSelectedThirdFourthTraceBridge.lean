import ImbalancedChen.P2OriginalSelectedPrefixCriticalSquares
import ImbalancedChen.P2OriginalLowerCompactTraceBinding

-- SOURCE ONLY / UNCOMPILED_ZERO_CREDIT / HELD.
-- A selected CandidateBank row carries its own SourceForm support mask.
-- The ordinary Trace stores only scalar caps and all-false physical marks;
-- neither its marks nor its BranchTable row are used as a selected mask.
-- This bridge starts after the first two original admissions have passed.
-- The third admission is the odd-rank bypass. Its chosen cap is frozen
-- before the fourth even-rank cube admission is tested.

namespace ImbalancedChen.P2OriginalSelectedThirdFourthTraceBridge

noncomputable section
open scoped Classical
open P2PhysicalIncomingPrefixCells P2LowerCapPlanIntegerRetention
open P2EnhancedLowerPhysicalNode
open P2OriginalLowerSelectedCapConstructor (Code BranchTable prefixCode)
open P2OriginalLowerCompactStartCapConstructor
open P2OriginalLowerCompactTraceBinding
open P2OriginalLowerWholeBoxBranchSelect
open P2OriginalLowerSelectedCriticalInterval
open P2OriginalCompactPhysicalGateTransfer
open P2OriginalSelectedMaskPhysicalSquares
open P2OriginalSelectedPrefixCriticalSquares

private theorem prefix_codeAt_three_actual (S : CompactStart)
    (mesh : ℕ) (x : Fin 5 → ℝ) :
    prefixCode 3 (codeAt S mesh 3 [x 0, x 1, x 2]) =
      prefixCode 3 (actualCode S mesh x) := by
  funext i
  fin_cases i <;>
    simp [prefixCode, actualCode, codeAt, incomingCode,
      physicalCode, marked]

private theorem cap3_prefix_congr (S : CompactStart) {mesh : ℕ}
    (table : BranchTable mesh) (rho : ℝ)
    (code₁ code₂ : Code mesh)
    (hcode : prefixCode 3 code₁ = prefixCode 3 code₂) :
    cap3 S table rho code₁ = cap3 S table rho code₂ := by
  simp [cap3, checkedCap, checkedChoice, hcode]

-- This is the literal first square and second even cube of the root run.
-- No rank-one or rank-two choice can change the baseline cap.
private theorem two_prefix_from_root (S : CompactStart)
    {mesh : ℕ} (table : BranchTable mesh) (rho : ℝ)
    (x : Fin 5 → ℝ)
    (hfirst : 2 * x 0 < baselineCap rho)
    (hsecond : x 0 + 3 * x 1 < baselineCap rho) :
    let P := compactPlan S table rho
    let H2 := run P (S.epsilon : ℝ) (startCutoff S.start : ℝ)
      (root (baselineCap rho)) [x 0, x 1]
    H2.word = [x 0, x 1] ∧
      H2.cap = baselineCap rho ∧ H2.accepted = true := by
  let P := compactPlan S table rho
  let H1 := step P (S.epsilon : ℝ) (startCutoff S.start : ℝ)
    (root (baselineCap rho)) (x 0)
  let H2 := step P (S.epsilon : ℝ) (startCutoff S.start : ℝ) H1 (x 1)
  have hw1 : H1.word = [x 0] := by simp [H1, step, root]
  have hc1 : H1.cap = baselineCap rho := by
    simpa [H1] using no_new_cap_outside_345 P
      (S.epsilon : ℝ) (startCutoff S.start : ℝ)
      (root (baselineCap rho)) (x 0) (by simp [root])
  have ha1 : H1.accepted = true := by
    apply (step_accepted_iff P (S.epsilon : ℝ)
      (startCutoff S.start : ℝ)
      (root (baselineCap rho)) (x 0)).mpr
    exact ⟨rfl, by simpa [admission, root] using hfirst⟩
  have hw2 : H2.word = [x 0, x 1] := by
    simp [H2, step, hw1]
  have hc2 : H2.cap = baselineCap rho := by
    have hc := no_new_cap_outside_345 P
      (S.epsilon : ℝ) (startCutoff S.start : ℝ) H1 (x 1)
      (by simp [hw1])
    exact hc.trans hc1
  have ha2 : H2.accepted = true := by
    apply (step_accepted_iff P (S.epsilon : ℝ)
      (startCutoff S.start : ℝ) H1 (x 1)).mpr
    refine ⟨ha1, ?_⟩
    simpa [admission, hw1, hc1] using hsecond
  change H2.word = [x 0, x 1] ∧
    H2.cap = baselineCap rho ∧ H2.accepted = true
  exact ⟨hw2, hc2, ha2⟩

-- The two-coordinate Trace is the actual chronology input; its accepted
-- flag states the initial square and second even cube have already passed.
-- No rank-three cube condition is inserted.
theorem third_selected_source_and_frozen_trace (S : CompactStart)
    {mesh : ℕ} (bank : CandidateBank mesh)
    (buffer : ℚ) (hbuffer : 0 < buffer)
    (rho : ℝ) (x : Fin 5 → ℝ)
    (hx : ∀ i, x i ∈ Set.Icc (S.epsilon : ℝ)
      (startCutoff S.start : ℝ))
    (data3 : P2OriginalLowerBufferedAffineBoxes.BranchData)
    (hsel3 : select S bank buffer 3
      (prefixCode 3 (actualCode S mesh x)) = some data3)
    (H2 : Trace) (hword2 : H2.word = [x 0, x 1])
    (hcap2 : H2.cap = baselineCap rho)
    (haccepted2 : H2.accepted = true) :
    let table := P2OriginalLowerCompactStartCapConstructor.boxedTable S
      (select S bank buffer) buffer
    let H3 := step (compactPlan S table rho)
      (S.epsilon : ℝ) (startCutoff S.start : ℝ) H2 (x 2)
    (∃ b3 ∈ bank.alternatives 3
        (prefixCode 3 (actualCode S mesh x)),
      supportCheck S 3 (prefixCode 3 (actualCode S mesh x))
        buffer b3 ∧ data3 = b3.asBranchData ∧
      SameBranchPointSquares S 3
        (prefixCode 3 (actualCode S mesh x)) buffer b3 x ∧
      CriticalInterval
        (bufferedCap S
          (prefixCode 3 (actualCode S mesh x)) buffer b3 : ℝ)
        (selectedSum b3.form.supportMask x)) ∧
    H3.word = [x 0, x 1, x 2] ∧
    H3.cap = cap3 S table rho (actualCode S mesh x) ∧
    H3.accepted = true := by
  let table := P2OriginalLowerCompactStartCapConstructor.boxedTable S
    (select S bank buffer) buffer
  let H3 := step (compactPlan S table rho)
    (S.epsilon : ℝ) (startCutoff S.start : ℝ) H2 (x 2)
  have hsource := selected_source_actual_squares_and_interval
    S bank buffer hbuffer 3 x hx data3 hsel3
  have hword3 : H3.word = [x 0, x 1, x 2] := by
    simp [H3, step, hword2]
  have hcode3 := prefix_codeAt_three_actual S mesh x
  have hcap3 : H3.cap = cap3 S table rho (actualCode S mesh x) := by
    have hstep := compact_step_three_cap S table rho (x 2) H2
      (by simp [hword2]) hcap2
    have hprefix : prefixCode 3
        (codeAt S mesh 3 (H2.word ++ [x 2])) =
        prefixCode 3 (actualCode S mesh x) := by
      simpa [hword2] using hcode3
    exact hstep.trans (cap3_prefix_congr S table rho _ _ hprefix)
  have haccepted3 : H3.accepted = true := by
    apply (step_accepted_iff (compactPlan S table rho)
      (S.epsilon : ℝ) (startCutoff S.start : ℝ) H2 (x 2)).mpr
    refine ⟨haccepted2, ?_⟩
    simp [admission, hword2]
  exact ⟨hsource, hword3, hcap3, haccepted3⟩

-- Both source rows are selected on the physical prefix codes. The fourth
-- even cube test reads H3.cap, fixed by the third step. The selected
-- subset square tests and inverse tent intervals use b3/b4 masks from
-- their own SourceForms; Trace.marked never supplies those masks.
theorem selected_third_fourth_actual_trace (S : CompactStart)
    {mesh : ℕ} (bank : CandidateBank mesh)
    (buffer : ℚ) (hbuffer : 0 < buffer)
    (rho : ℝ) (x : Fin 5 → ℝ)
    (hx : ∀ i, x i ∈ Set.Icc (S.epsilon : ℝ)
      (startCutoff S.start : ℝ))
    (hsmall : rho < (249 / 448 : ℝ) - 3 * (19 / 125 : ℝ))
    (data3 data4 : P2OriginalLowerBufferedAffineBoxes.BranchData)
    (hsel3 : select S bank buffer 3
      (prefixCode 3 (actualCode S mesh x)) = some data3)
    (hsel4 : select S bank buffer 4
      (prefixCode 4 (actualCode S mesh x)) = some data4)
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
    :
    let table := P2OriginalLowerCompactStartCapConstructor.boxedTable S
      (select S bank buffer) buffer
    let H2 := run (compactPlan S table rho)
      (S.epsilon : ℝ) (startCutoff S.start : ℝ)
      (root (baselineCap rho)) [x 0, x 1]
    let H3 := step (compactPlan S table rho)
      (S.epsilon : ℝ) (startCutoff S.start : ℝ) H2 (x 2)
    let H4 := step (compactPlan S table rho)
      (S.epsilon : ℝ) (startCutoff S.start : ℝ) H3 (x 3)
    (∃ b3 ∈ bank.alternatives 3
        (prefixCode 3 (actualCode S mesh x)),
      supportCheck S 3 (prefixCode 3 (actualCode S mesh x))
        buffer b3 ∧ data3 = b3.asBranchData ∧
      SameBranchPointSquares S 3
        (prefixCode 3 (actualCode S mesh x)) buffer b3 x ∧
      CriticalInterval
        (bufferedCap S
          (prefixCode 3 (actualCode S mesh x)) buffer b3 : ℝ)
        (selectedSum b3.form.supportMask x)) ∧
    (∃ b4 ∈ bank.alternatives 4
        (prefixCode 4 (actualCode S mesh x)),
      supportCheck S 4 (prefixCode 4 (actualCode S mesh x))
        buffer b4 ∧ data4 = b4.asBranchData ∧
      SameBranchPointSquares S 4
        (prefixCode 4 (actualCode S mesh x)) buffer b4 x ∧
      CriticalInterval
        (bufferedCap S
          (prefixCode 4 (actualCode S mesh x)) buffer b4 : ℝ)
        (selectedSum b4.form.supportMask x)) ∧
    H3.cap = cap3 S table rho (actualCode S mesh x) ∧
    H3.accepted = true ∧
    x 0 + x 1 + x 2 + 3 * x 3 < H3.cap ∧
    H4.accepted = true := by
  let table := P2OriginalLowerCompactStartCapConstructor.boxedTable S
    (select S bank buffer) buffer
  let H2 := run (compactPlan S table rho)
    (S.epsilon : ℝ) (startCutoff S.start : ℝ)
    (root (baselineCap rho)) [x 0, x 1]
  let H3 := step (compactPlan S table rho)
    (S.epsilon : ℝ) (startCutoff S.start : ℝ) H2 (x 2)
  let H4 := step (compactPlan S table rho)
    (S.epsilon : ℝ) (startCutoff S.start : ℝ) H3 (x 3)
  have hphysical := actual_five_word_historical_gates S table rho x hx
    hsmall hthird hfourth
  obtain ⟨hword2, hcap2, haccepted2⟩ :=
    two_prefix_from_root S table rho x hphysical.1 hphysical.2.1
  obtain ⟨hsource3, hword3, hcap3, haccepted3⟩ :=
    third_selected_source_and_frozen_trace S bank buffer hbuffer
      rho x hx data3 hsel3 H2 hword2 hcap2 haccepted2
  have hsource4 := selected_source_actual_squares_and_interval
    S bank buffer hbuffer 4 x hx data4 hsel4
  have hcube : x 0 + x 1 + x 2 + 3 * x 3 < H3.cap := by
    rw [hcap3]
    exact hphysical.2.2
  have haccepted4 : H4.accepted = true :=
    selected_fourth_actual_trace_passes S table rho x hx hsmall
      hthird hfourth H3 hword3 hcap3 haccepted3
  exact ⟨hsource3, hsource4, hcap3, haccepted3, hcube, haccepted4⟩

end
end ImbalancedChen.P2OriginalSelectedThirdFourthTraceBridge
