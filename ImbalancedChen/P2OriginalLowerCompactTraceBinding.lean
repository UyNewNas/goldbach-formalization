import ImbalancedChen.P2OriginalLowerCompactStartCapConstructor
import ImbalancedChen.P2LowerCapPlanIntegerRetention

-- SOURCE ONLY / UNCOMPILED_ZERO_CREDIT.
-- Corrected original L1/L2 compact-start physical trace. The mesh starts
-- at epsilon<w, so selected exponents below a are represented for L1.
-- A fresh cap is frozen after the current square/even-cube admission.

namespace ImbalancedChen.P2OriginalLowerCompactTraceBinding

noncomputable section
open P2PhysicalIncomingPrefixCells P2LowerCapPlanIntegerRetention
open P2OriginalLowerSelectedCapConstructor
open P2OriginalLowerCompactStartCapConstructor

def codeAt (S : CompactStart) (mesh rank : ℕ) (word : List ℝ) : Code mesh :=
  incomingCode (S.epsilon : ℝ) (startCutoff S.start : ℝ)
    5 mesh rank (marked word)

theorem compact_choice_three (S : CompactStart) {mesh : ℕ}
    (table : BranchTable mesh) (rho : ℝ) (word : List ℝ)
    (hlen : word.length = 3) :
    planChoice (compactPlan S table rho)
      (S.epsilon : ℝ) (startCutoff S.start : ℝ) word =
      checkedChoice S table 3 (baselineCap rho) (codeAt S mesh 3 word) := by
  simp [planChoice, hlen, incomingChoice, compactPlan, codeAt]

theorem compact_choice_four (S : CompactStart) {mesh : ℕ}
    (table : BranchTable mesh) (rho : ℝ) (word : List ℝ)
    (hlen : word.length = 4) :
    planChoice (compactPlan S table rho)
      (S.epsilon : ℝ) (startCutoff S.start : ℝ) word =
      checkedChoice S table 4
        (cap3 S table rho (codeAt S mesh 4 word))
        (codeAt S mesh 4 word) := by
  simp [planChoice, hlen, incomingChoice, compactPlan, codeAt]

theorem compact_choice_five (S : CompactStart) {mesh : ℕ}
    (table : BranchTable mesh) (rho : ℝ) (word : List ℝ)
    (hlen : word.length = 5) :
    planChoice (compactPlan S table rho)
      (S.epsilon : ℝ) (startCutoff S.start : ℝ) word =
      checkedChoice S table 5
        (cap4 S table rho (codeAt S mesh 5 word))
        (codeAt S mesh 5 word) := by
  simp [planChoice, hlen, incomingChoice, compactPlan, codeAt]

theorem compact_step_three_cap (S : CompactStart) {mesh : ℕ}
    (table : BranchTable mesh) (rho x : ℝ) (H : Trace)
    (hlen : H.word.length = 2) (hcap : H.cap = baselineCap rho) :
    (step (compactPlan S table rho)
      (S.epsilon : ℝ) (startCutoff S.start : ℝ) H x).cap =
      cap3 S table rho (codeAt S mesh 3 (H.word ++ [x])) := by
  have h3 : (H.word ++ [x]).length = 3 := by simp [hlen]
  change (planChoice (compactPlan S table rho)
    (S.epsilon : ℝ) (startCutoff S.start : ℝ)
      (H.word ++ [x])).freeze H.cap = _
  rw [hcap, compact_choice_three S table rho (H.word ++ [x]) h3]
  rfl

theorem compact_step_four_cap (S : CompactStart) {mesh : ℕ}
    (table : BranchTable mesh) (rho x : ℝ) (H : Trace)
    (hlen : H.word.length = 3)
    (hcap : H.cap = cap3 S table rho (codeAt S mesh 4 (H.word ++ [x]))) :
    (step (compactPlan S table rho)
      (S.epsilon : ℝ) (startCutoff S.start : ℝ) H x).cap =
      cap4 S table rho (codeAt S mesh 4 (H.word ++ [x])) := by
  have h4 : (H.word ++ [x]).length = 4 := by simp [hlen]
  change (planChoice (compactPlan S table rho)
    (S.epsilon : ℝ) (startCutoff S.start : ℝ)
      (H.word ++ [x])).freeze H.cap = _
  rw [hcap, compact_choice_four S table rho (H.word ++ [x]) h4]
  rfl

theorem compact_step_five_cap (S : CompactStart) {mesh : ℕ}
    (table : BranchTable mesh) (rho x : ℝ) (H : Trace)
    (hlen : H.word.length = 4)
    (hcap : H.cap = cap4 S table rho (codeAt S mesh 5 (H.word ++ [x]))) :
    (step (compactPlan S table rho)
      (S.epsilon : ℝ) (startCutoff S.start : ℝ) H x).cap =
      cap5 S table rho (codeAt S mesh 5 (H.word ++ [x])) := by
  have h5 : (H.word ++ [x]).length = 5 := by simp [hlen]
  change (planChoice (compactPlan S table rho)
    (S.epsilon : ℝ) (startCutoff S.start : ℝ)
      (H.word ++ [x])).freeze H.cap = _
  rw [hcap, compact_choice_five S table rho (H.word ++ [x]) h5]
  rfl

end
end ImbalancedChen.P2OriginalLowerCompactTraceBinding
