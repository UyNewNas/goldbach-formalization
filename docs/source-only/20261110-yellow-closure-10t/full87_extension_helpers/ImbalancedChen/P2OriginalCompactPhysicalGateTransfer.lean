import ImbalancedChen.P2OriginalLowerCompactTraceBinding
import ImbalancedChen.P2OriginalSelectedBoxGateMargin

-- SOURCE ONLY / UNCOMPILED_ZERO_CREDIT / HELD.
-- The compact code covers both lower starts on [epsilon,w], including L1
-- exponents below a. Fresh rank-three/four choices yield historical gates
-- at their actual incoming caps. Inherit choices and the odd-rank bypass
-- remain those of the imported Trace/CapPlan; no new cube is imposed.
-- Literal selected BranchTable rows are still not supplied here. Moreover,
-- Trace.marked assigns false to every physical coordinate and the current
-- BranchTable carries only (cap,argument), not a support mask. Hence this
-- source transfers historical full gates only; selected-subset licence
-- needs a separate branch-mask witness and selector proof.

namespace ImbalancedChen.P2OriginalCompactPhysicalGateTransfer

noncomputable section
open P2PhysicalIncomingPrefixCells P2LowerCapPlanIntegerRetention
open P2OriginalLowerSelectedCapConstructor (Code BranchTable prefixCode)
open P2OriginalLowerCompactStartCapConstructor
open P2OriginalLowerCompactTraceBinding P2OriginalSelectedBoxGateMargin

def upper (S : CompactStart) {mesh : ℕ}
    (code : Code mesh) (i : Fin 5) : ℝ :=
  P2OriginalLowerCompactStartCapConstructor.cellUpper S mesh (code i).1

def actualCode (S : CompactStart) (mesh : ℕ)
    (x : Fin 5 → ℝ) : Code mesh :=
  codeAt S mesh 5 [x 0, x 1, x 2, x 3, x 4]

-- Every physical coordinate on the paper's compact [epsilon,w] domain
-- lies below the very endpoint stored by the selected-plan code.
theorem actual_five_word_below_upper (S : CompactStart) {mesh : ℕ}
    (x : Fin 5 → ℝ)
    (hx : ∀ i, x i ∈ Set.Icc (S.epsilon : ℝ)
      (startCutoff S.start : ℝ)) :
    ∀ i, x i ≤ upper S (actualCode S mesh x) i := by
  intro i
  fin_cases i <;>
    simpa [upper, actualCode, codeAt, incomingCode, physicalCode, marked]
      using mem_exponentCell_le_upper S mesh
        (exponentCode_membership (hx i))

theorem integer_physical_word_below_upper (S : CompactStart)
    {mesh N : ℕ} (history : List ℕ) (x : Fin 5 → ℝ)
    (hword : physicalWord N history =
      [x 0, x 1, x 2, x 3, x 4])
    (hx : ∀ i, x i ∈ Set.Icc (S.epsilon : ℝ)
      (startCutoff S.start : ℝ)) :
    ∀ i, x i ≤ upper S
      (codeAt S mesh 5 (physicalWord N history)) i := by
  simpa [actualCode, hword] using actual_five_word_below_upper S x hx

theorem cellUpper_le_start (S : CompactStart) {mesh : ℕ}
    (c : CellCode mesh) :
    P2OriginalLowerCompactStartCapConstructor.cellUpper S mesh c ≤
      (startCutoff S.start : ℝ) := by
  cases c with
  | none => rfl
  | some j =>
      have hs : (S.epsilon : ℝ) < (startCutoff S.start : ℝ) := by
        exact_mod_cast S.epsilon_lt_start
      exact (logPrimeMeshLoHi_bounds (d := 1) hs mesh
        (fun _ => j) 0).2.2

-- A fresh checkedChoice exposes the primitive rational row and its
-- actual whole-box guards. No selected gain or complete table is assumed.
theorem fresh_has_branch_gates (S : CompactStart) {mesh : ℕ}
    (table : BranchTable mesh) (rank : Fin 6)
    (parent : ℝ) (code : Code mesh)
    (hfresh : ∃ c s : ℝ,
      checkedChoice S table rank parent code = .fresh c s) :
    ∃ c s : ℚ,
      table.row rank (prefixCode rank.val code) = some (c,s) ∧
      branchGates S rank parent c (prefixCode rank.val code) := by
  rcases hfresh with ⟨c,s,hfresh⟩
  cases hr : table.row rank (prefixCode rank.val code) with
  | none => simp [checkedChoice, hr] at hfresh
  | some pair =>
      rcases pair with ⟨candidate,argument⟩
      by_cases hg : branchGates S rank parent candidate
          (prefixCode rank.val code)
      · exact ⟨candidate,argument,hr,hg⟩
      · simp [checkedChoice,hr,hg] at hfresh

-- Positive slack is constructed from actual checked whole-box gaps.
-- This is the corrected counterpart of the prior [a,h] conditional leaf.
theorem fresh_choices_strict_corner (S : CompactStart) {mesh : ℕ}
    (table : BranchTable mesh) (rho : ℝ) (x : Fin 5 → ℝ)
    (hsmall : rho < (249 / 448 : ℝ) - 3 * (19 / 125 : ℝ))
    (hthird : ∃ c s : ℝ,
      checkedChoice S table 3 (baselineCap rho)
        (actualCode S mesh x) = .fresh c s)
    (hfourth : ∃ c s : ℝ,
      checkedChoice S table 4
        (cap3 S table rho (actualCode S mesh x))
        (actualCode S mesh x) = .fresh c s) :
    ∃ delta : ℝ, StrictUpperCorner
      (upper S (actualCode S mesh x)) (baselineCap rho)
      (cap3 S table rho (actualCode S mesh x)) delta := by
  let code := actualCode S mesh x
  let u := upper S code
  obtain ⟨_, _, _, g3⟩ :=
    fresh_has_branch_gates S table 3 (baselineCap rho) code hthird
  obtain ⟨_, _, _, g4⟩ :=
    fresh_has_branch_gates S table 4 (cap3 S table rho code) code hfourth
  have hsecond : u 0 + 3 * u 1 < baselineCap rho := by
    simpa [historicalGate, prefixCode, u, upper] using g3.2.2.1
  have hfour : u 0 + u 1 + u 2 + 3 * u 3 <
      cap3 S table rho code := by
    simpa [historicalGate, prefixCode, u, upper] using g4.2.2.1
  have hu0 : u 0 ≤ (startCutoff S.start : ℝ) :=
    cellUpper_le_start S (code 0).1
  have hw : (startCutoff S.start : ℝ) ≤ (19 / 125 : ℝ) := by
    cases S.start <;> norm_num [startCutoff]
  have hfirst : 2 * u 0 < baselineCap rho := by
    dsimp [baselineCap]
    linarith
  let g1 := baselineCap rho - 2 * u 0
  let g2 := baselineCap rho - u 0 - 3 * u 1
  let g3' := cap3 S table rho code - u 0 - u 1 - u 2 - 3 * u 3
  let delta := min g1 (min g2 g3') / 2
  have hg : 0 < min g1 (min g2 g3') := by
    apply lt_min
    · dsimp [g1]; linarith
    · apply lt_min
      · dsimp [g2]; linarith
      · dsimp [g3']; linarith
  have hd : 0 < delta := by dsimp [delta]; linarith
  refine ⟨delta, ⟨hd, ?_, ?_, ?_⟩⟩
  · have hm := min_le_left g1 (min g2 g3')
    dsimp [delta, g1] at *
    linarith
  · have hm := (min_le_right g1 (min g2 g3')).trans
      (min_le_left g2 g3')
    dsimp [delta, g2] at *
    linarith
  · have hm := (min_le_right g1 (min g2 g3')).trans
      (min_le_right g2 g3')
    dsimp [delta, g3'] at *
    linarith

theorem actual_five_word_historical_gates (S : CompactStart) {mesh : ℕ}
    (table : BranchTable mesh) (rho : ℝ) (x : Fin 5 → ℝ)
    (hx : ∀ i, x i ∈ Set.Icc (S.epsilon : ℝ)
      (startCutoff S.start : ℝ))
    (hsmall : rho < (249 / 448 : ℝ) - 3 * (19 / 125 : ℝ))
    (hthird : ∃ c s : ℝ,
      checkedChoice S table 3 (baselineCap rho)
        (actualCode S mesh x) = .fresh c s)
    (hfourth : ∃ c s : ℝ,
      checkedChoice S table 4
        (cap3 S table rho (actualCode S mesh x))
        (actualCode S mesh x) = .fresh c s) :
    2 * x 0 < baselineCap rho ∧
      x 0 + 3 * x 1 < baselineCap rho ∧
      x 0 + x 1 + x 2 + 3 * x 3 <
        cap3 S table rho (actualCode S mesh x) := by
  obtain ⟨delta, hcorner⟩ :=
    fresh_choices_strict_corner S table rho x hsmall hthird hfourth
  exact point_gates_of_strict_upper_corner hcorner
    (actual_five_word_below_upper S x hx)

theorem selected_fourth_actual_trace_passes (S : CompactStart) {mesh : ℕ}
    (table : BranchTable mesh) (rho : ℝ) (x : Fin 5 → ℝ)
    (hx : ∀ i, x i ∈ Set.Icc (S.epsilon : ℝ)
      (startCutoff S.start : ℝ))
    (hsmall : rho < (249 / 448 : ℝ) - 3 * (19 / 125 : ℝ))
    (hthird : ∃ c s : ℝ,
      checkedChoice S table 3 (baselineCap rho)
        (actualCode S mesh x) = .fresh c s)
    (hfourth : ∃ c s : ℝ,
      checkedChoice S table 4
        (cap3 S table rho (actualCode S mesh x))
        (actualCode S mesh x) = .fresh c s)
    (H : Trace) (hword : H.word = [x 0, x 1, x 2])
    (hincoming : H.cap = cap3 S table rho (actualCode S mesh x))
    (haccepted : H.accepted = true) :
    (step (compactPlan S table rho)
      (S.epsilon : ℝ) (startCutoff S.start : ℝ)
      H (x 3)).accepted = true := by
  have hcube :=
    (actual_five_word_historical_gates S table rho x hx
      hsmall hthird hfourth).2.2
  apply (step_accepted_iff (compactPlan S table rho)
    (S.epsilon : ℝ) (startCutoff S.start : ℝ) H (x 3)).mpr
  refine ⟨haccepted, ?_⟩
  simpa [admission, hword, hincoming, add_assoc] using hcube

end
end ImbalancedChen.P2OriginalCompactPhysicalGateTransfer
