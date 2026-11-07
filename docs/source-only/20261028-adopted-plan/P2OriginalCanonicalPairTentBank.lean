import ImbalancedChen.P2OriginalPairSourceReceiver
import ImbalancedChen.P2OriginalFiniteTentBankSelectorMargins
import ImbalancedChen.ActualSelectedSubproductParameters

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

A concrete finite source bank for the original tent subfamily. There is
no CandidateBank, selected policy, successful selection or final gain
input. The original rank-eligible masks are enumerated; each mask first
chooses the LOWER affine side of v, then passes its own full/selected
square screen. The higher sibling never enters the maximization.

The bank's comparison floor is the fixed initial cap. At ranks four and
five this is only a source-ranking floor: the imported pairPlan ALWAYS
retests a fresh action against its own actual frozen preceding cap.
Equality with that actual parent therefore inherits literally.

The literal witness below has a selected {0,1} third tent, not an empty
filtered bank. It also passes the ordinary first square and second cube.
This supplies a finite cap/retention program instance, not the complete
arithmetic compiler, nor the entire
adopted W/tent policy, historical L5/L6 bank, or its numerical gain.
The stored argument retains the existing tent-bank selected-sum midpoint;
it is NOT identified here with a residual Buchstab/H/h query. Accordingly
the proved application concerns cap/retention geometry, not a query floor.
-/

namespace ImbalancedChen.P2OriginalCanonicalPairTentBank

noncomputable section
open scoped Classical BigOperators
open P2PhysicalIncomingPrefixCells P2LowerCapPlanIntegerRetention
open P2OriginalPairSourceReceiver
open P2OriginalLowerWholeBoxBranchSelect
open P2OriginalLowerBufferedAffineBoxes
open P2OriginalLowerAffineTieSelector
open P2EnhancedLowerPhysicalNode
open P2OriginalLowerSelectedCapConstructor (Code prefixCode strictSquareGates)
open P2OriginalFiniteTentBankSelectorMargins (tentMasks maskNumber)

def selectedMid (R : PairRange) {mesh : ℕ} (code : Code mesh)
    (mask : Finset (Fin 5)) : ℚ :=
  ((∑ i ∈ mask, qLo R mesh (code i).1) +
    (∑ i ∈ mask, qHi R mesh (code i).1)) / 2

def leftRow (R : PairRange) {mesh : ℕ} (code : Code mesh)
    (mask : Finset (Fin 5)) : SelectedBranchData :=
  ⟨maskNumber mask, .tentLeft mask, selectedMid R code mask⟩

def rightRow (R : PairRange) {mesh : ℕ} (code : Code mesh)
    (mask : Finset (Fin 5)) : SelectedBranchData :=
  ⟨maskNumber mask, .tentRight mask, selectedMid R code mask⟩

/-- One mask gives one composite tent. Identical-side equality takes left;
    a crossing box supplies no action and remains available to inherit. -/
def lowerSide (R : PairRange) {mesh : ℕ} (code : Code mesh)
    (mask : Finset (Fin 5)) : Option SelectedBranchData :=
  let l := leftRow R code mask
  let r := rightRow R code mask
  if 0 ≤ gapLower r.cap l.cap (box R code) then some l
  else if 0 ≤ gapLower l.cap r.cap (box R code) then some r else none

theorem lowerSide_source (R : PairRange) {mesh : ℕ} (code : Code mesh)
    (mask : Finset (Fin 5)) (b : SelectedBranchData)
    (h : lowerSide R code mask = some b) :
    (b = leftRow R code mask ∨ b = rightRow R code mask) ∧
      sideCheck b (box R code) ∧ b.form.supportMask = mask := by
  unfold lowerSide at h
  split_ifs at h with hl hr
  · have hb : b = leftRow R code mask := Option.some_inj.mp h.symm
    subst b
    exact ⟨Or.inl rfl, hl, rfl⟩
  · have hb : b = rightRow R code mask := Option.some_inj.mp h.symm
    subst b
    exact ⟨Or.inr rfl, hr, rfl⟩
  · simp at h

theorem lowerSide_eval_is_tent (R : PairRange) {mesh : ℕ}
    (code : Code mesh) (mask : Finset (Fin 5)) (b : SelectedBranchData)
    (h : lowerSide R code mask = some b) (x : Fin 5 → ℝ)
    (hx : inBox (box R code) x) :
    b.cap.eval x = min
      (SourceForm.affine (.tentLeft mask)).eval x
      (SourceForm.affine (.tentRight mask)).eval x := by
  obtain ⟨hrow, hside, _⟩ := lowerSide_source R code mask b h
  rcases hrow with rfl | rfl
  · apply (min_eq_left _).symm
    exact sideCheck_sound (leftRow R code mask) (box R code) x hside hx
      (SourceForm.affine (.tentRight mask)) rfl
  · apply (min_eq_right _).symm
    exact sideCheck_sound (rightRow R code mask) (box R code) x hside hx
      (SourceForm.affine (.tentLeft mask)) rfl

private theorem left_eval_actual (mask : Finset (Fin 5)) (x : Fin 5 → ℝ) :
    (SourceForm.affine (.tentLeft mask)).eval x =
      VariableEnvelope.A (∑ i ∈ mask, x i) := by
  fin_cases mask <;>
    simp [SourceForm.affine,AffineBranch.eval,VariableEnvelope.A,
      Fin.sum_univ_succ] <;> ring

private theorem right_eval_actual (mask : Finset (Fin 5)) (x : Fin 5 → ℝ) :
    (SourceForm.affine (.tentRight mask)).eval x =
      VariableEnvelope.C (∑ i ∈ mask, x i) := by
  fin_cases mask <;>
    simp [SourceForm.affine,AffineBranch.eval,VariableEnvelope.C,
      Fin.sum_univ_succ] <;> ring

theorem lowerSide_eval_actual_v (R : PairRange) {mesh : ℕ}
    (code : Code mesh) (mask : Finset (Fin 5)) (b : SelectedBranchData)
    (h : lowerSide R code mask = some b) (x : Fin 5 → ℝ)
    (hx : inBox (box R code) x) :
    b.cap.eval x = VariableEnvelope.v (∑ i ∈ mask, x i) := by
  rw [lowerSide_eval_is_tent R code mask b h x hx,
    left_eval_actual,right_eval_actual,VariableEnvelope.v_eq_min]

def screened (R : PairRange) {mesh : ℕ} (buffer : ℚ) (rank : Fin 6)
    (code : Code mesh) (mask : Finset (Fin 5)) : Option SelectedBranchData :=
  match lowerSide R code mask with
  | none => none
  | some b => if sourceCheck R rank code buffer b then some b else none

def alternatives (R : PairRange) {mesh : ℕ} (buffer : ℚ)
    (rank : Fin 6) (code : Code mesh) : List SelectedBranchData :=
  (tentMasks rank).toList.flatMap (fun mask => (screened R buffer rank code mask).toList)

def initialRow (seed : ℚ) : LabeledBranch 5 :=
  ⟨0, ⟨seed, fun _ => 0⟩, 2⟩

/-- All choices and source forms are computed from the original finite
    mask alphabet, physical grid, buffer and fixed initial cap. -/
def bank (R : PairRange) (mesh : ℕ) (buffer seed : ℚ) : CandidateBank mesh :=
  ⟨fun _ _ => initialRow seed, alternatives R buffer⟩

def plan (R : PairRange) (mesh : ℕ) (buffer seed : ℚ) : CapPlan 5 mesh :=
  pairPlan R (bank R mesh buffer seed) buffer (seed : ℝ)

theorem original_mask_alphabet (rank : Fin 6) (mask : Finset (Fin 5)) :
    mask ∈ tentMasks rank ↔ formRankEligible rank (.tentLeft mask) := by
  simp [tentMasks]

theorem original_mask_counts :
    (tentMasks 3).card = 7 ∧ (tentMasks 4).card = 8 ∧ (tentMasks 5).card = 16 := by
  decide +kernel

theorem every_screened_original_action_occurs (R : PairRange) (mesh : ℕ)
    (buffer seed : ℚ) (rank : Fin 6) (code : Code mesh)
    (mask : Finset (Fin 5)) (hm : mask ∈ tentMasks rank)
    (b : SelectedBranchData) (hside : lowerSide R code mask = some b)
    (hcheck : sourceCheck R rank code buffer b) :
    b ∈ (bank R mesh buffer seed).alternatives rank code := by
  apply List.mem_flatMap.mpr
  exact ⟨mask,Finset.mem_toList.mpr hm,by simp [screened,hside,hcheck]⟩

def outputAlphabet (R : PairRange) (mesh : ℕ) (buffer seed : ℚ) : Finset CapChoice :=
  Finset.univ.image (fun p : Fin 6 × Code mesh =>
    (plan R mesh buffer seed).choose p.1 p.2)

theorem choice_mem_fixed_outputAlphabet (R : PairRange) (mesh : ℕ)
    (buffer seed : ℚ) (rank : Fin 6) (code : Code mesh) :
    (plan R mesh buffer seed).choose rank code ∈ outputAlphabet R mesh buffer seed := by
  exact Finset.mem_image.mpr ⟨(rank,code),Finset.mem_univ _,rfl⟩

theorem concrete_plan_future_invariant (R : PairRange) (mesh : ℕ)
    (buffer seed : ℚ) (rank : ℕ) (parent future : List MarkedExponent)
    (hr : rank ≤ parent.length) :
    incomingChoice (plan R mesh buffer seed) R.epsilon ceiling rank (parent++future) =
      incomingChoice (plan R mesh buffer seed) R.epsilon ceiling rank parent :=
  incomingChoice_future_invariant (plan R mesh buffer seed) _ _ rank parent future hr

theorem alternatives_source (R : PairRange) {mesh : ℕ} (buffer : ℚ)
    (rank : Fin 6) (code : Code mesh) (b : SelectedBranchData)
    (hb : b ∈ alternatives R buffer rank code) :
    ∃ mask ∈ tentMasks rank, lowerSide R code mask = some b ∧
      sourceCheck R rank code buffer b ∧ b.form.supportMask = mask := by
  obtain ⟨mask, hm, hb⟩ := List.mem_flatMap.mp hb
  have hmask := Finset.mem_toList.mp hm
  unfold screened at hb
  cases hs : lowerSide R code mask with
  | none => simp [hs] at hb
  | some c =>
      by_cases hc : sourceCheck R rank code buffer c
      · simp [hs, hc] at hb
        subst b
        exact ⟨mask, hmask, hs, hc, (lowerSide_source R code mask c hs).2.2⟩
      · simp [hs, hc] at hb

/-- Source identity, actual source mask and its full/selected gates survive
    the concrete selector. There is no supplied bank or selector witness
    among the constructor's inputs. -/
theorem selected_source (R : PairRange) (mesh : ℕ) (buffer seed : ℚ)
    (rank : Fin 6) (code : Code mesh) (b : SelectedBranchData)
    (hsel : select R (bank R mesh buffer seed) buffer rank code = some b) :
    ∃ mask ∈ tentMasks rank,
      lowerSide R (prefixCode rank.val code) mask = some b ∧
      sourceCheck R rank (prefixCode rank.val code) buffer b ∧
      b.form.supportMask = mask := by
  exact alternatives_source R buffer rank _ b
    (select_some_source R (bank R mesh buffer seed) buffer rank code b hsel).1

/-- A selected endpoint lies STRICTLY below its unchanged ORIGINAL tent
    source. This is a subfamily/source inclusion, not equality with the
    manuscript's common maximum, which also retains W branches. -/
theorem selected_endpoint_below_original_tent (R : PairRange) (mesh : ℕ)
    (buffer seed : ℚ) (hbuffer : 0 < buffer) (rank : Fin 6)
    (code : Code mesh) (b : SelectedBranchData)
    (hsel : select R (bank R mesh buffer seed) buffer rank code = some b)
    (x : Fin 5 → ℝ) (hx : inBox (box R (prefixCode rank.val code)) x) :
    ∃ mask ∈ tentMasks rank, b.form.supportMask = mask ∧
      (rowCap R (prefixCode rank.val code) buffer b : ℝ) <
        VariableEnvelope.v (∑ i ∈ mask, x i) := by
  obtain ⟨mask,hm,hside,_,hmask⟩ := selected_source R mesh buffer seed rank code b hsel
  have heval := lowerSide_eval_actual_v R _ mask b hside x hx
  have hinf := wholeBoxInfimum_le_affine b.cap.constant b.cap.slope
    (box R (prefixCode rank.val code)) x hx
  have hinf' : (wholeBoxInfimum b.cap.constant b.cap.slope
      (box R (prefixCode rank.val code)):ℝ) ≤ b.cap.eval x := by
    simpa [affineValue,AffineBranch.eval] using hinf
  have hb : (0:ℝ) < (buffer:ℝ) := by exact_mod_cast hbuffer
  refine ⟨mask,hm,hmask,?_⟩
  rw [← heval]
  change ((wholeBoxInfimum b.cap.constant b.cap.slope
    (box R (prefixCode rank.val code)) - buffer : ℚ):ℝ) < _
  push_cast
  linarith

/-- Actual inheritance has priority even when the source selector finds
    a tent equal to or below a previously frozen, larger parent cap. -/
theorem parent_priority (R : PairRange) (mesh : ℕ) (buffer seed : ℚ)
    (rank : Fin 6) (code : Code mesh) (parent : ℝ)
    (h : ∀ b, select R (bank R mesh buffer seed) buffer rank
        (prefixCode rank.val code) = some b →
      (rowCap R (prefixCode rank.val code) buffer b : ℝ) ≤ parent) :
    checkedChoice R (bank R mesh buffer seed) buffer rank parent code = .inherit 2 := by
  unfold checkedChoice
  cases hs : select R (bank R mesh buffer seed) buffer rank
      (prefixCode rank.val code) with
  | none => simp [hs]
  | some b =>
      have hn : ¬ freshCheck R rank (prefixCode rank.val code) buffer parent b := by
        intro hf
        exact (not_lt_of_ge (h b hs)) hf.1
      simp [hs, hn]

theorem checked_cap_mono (R : PairRange) (mesh : ℕ) (buffer seed : ℚ)
    (rank : Fin 6) (code : Code mesh) (parent : ℝ) :
    parent ≤ checkedCap R (bank R mesh buffer seed) buffer rank parent code := by
  unfold checkedCap checkedChoice
  cases hs : select R (bank R mesh buffer seed) buffer rank
      (prefixCode rank.val code) with
  | none => simp [hs, CapChoice.freeze]
  | some b =>
      by_cases hf : freshCheck R rank (prefixCode rank.val code) buffer parent b
      · simpa [hs, hf, CapChoice.freeze] using hf.1.le
      · simp [hs, hf, CapChoice.freeze]

theorem actual_parent_chain (R : PairRange) (mesh : ℕ) (buffer seed : ℚ)
    (code : Code mesh) (hseed : (seed : ℝ) ≤ 153/256) :
    (seed : ℝ) ≤ cap3 R (bank R mesh buffer seed) buffer seed code ∧
      cap3 R (bank R mesh buffer seed) buffer seed code ≤
        cap4 R (bank R mesh buffer seed) buffer seed code ∧
      cap4 R (bank R mesh buffer seed) buffer seed code ≤
        cap5 R (bank R mesh buffer seed) buffer seed code ∧
      cap5 R (bank R mesh buffer seed) buffer seed code ≤ 153/256 := by
  exact ⟨checked_cap_mono R mesh buffer seed 3 code seed,
    checked_cap_mono R mesh buffer seed 4 code _,
    checked_cap_mono R mesh buffer seed 5 code _,
    (caps_bounded R (bank R mesh buffer seed) buffer seed hseed code).2.2⟩

theorem actual_fifth_cap (R : PairRange) (mesh : ℕ) (buffer seed : ℚ)
    (x0 x1 x2 x3 x4 : ℝ) :
    (run (plan R mesh buffer seed) R.epsilon ceiling
      ⟨[x0,x1],seed,[],true⟩ [x2,x3,x4]).cap =
      cap5 R (bank R mesh buffer seed) buffer seed
        (codeAt R mesh 5 [x0,x1,x2,x3,x4]) :=
  pair_run_three_cap R (bank R mesh buffer seed) buffer seed x0 x1 x2 x3 x4

/-! A literal nonempty original-tent chamber. The mesh step is 1/1000;
    its first three intervals are [.100,.101], [.080,.081], [.040,.041].
    The {0,1} sum stays on the left tent side and strictly beats all
    other eligible masks throughout the entire closed box. -/

def witnessRange : PairRange := ⟨1/100, by norm_num, by norm_num⟩
def witnessBuffer : ℚ := 1/1000
def witnessSeed : ℚ := 249/448 - 1/1000
def witnessCode : Code 225 := fun i =>
  (if i = 0 then some ⟨90, by decide⟩
    else if i = 1 then some ⟨70, by decide⟩
    else if i = 2 then some ⟨30, by decide⟩ else none, false)
def witnessMask : Finset (Fin 5) := {0,1}
def witnessRow : SelectedBranchData := leftRow witnessRange witnessCode witnessMask
def witnessPoint : Fin 5 → ℝ := ![1/10, 2/25, 1/25, 59/250, 59/250]

theorem witness_prefix : prefixCode 3 witnessCode = witnessCode := by
  funext i
  fin_cases i <;> norm_num [prefixCode, witnessCode]

theorem witness_in_box : inBox (box witnessRange witnessCode) witnessPoint := by
  intro i
  fin_cases i <;> norm_num [inBox, box, qLo, qHi, qPoint, witnessRange,
    witnessCode, witnessPoint, ceiling]

theorem witness_lower_side :
    lowerSide witnessRange witnessCode witnessMask = some witnessRow := by
  norm_num [lowerSide, witnessRow, leftRow, rightRow, witnessMask, selectedMid,
    SelectedBranchData.cap, SourceForm.affine, gapLower, wholeBoxInfimum,
    box, qLo, qHi, qPoint, witnessCode, witnessRange, ceiling,
    Fin.sum_univ_succ]

theorem witness_source_check :
    sourceCheck witnessRange 3 witnessCode witnessBuffer witnessRow := by
  norm_num [sourceCheck, formRankEligible, sideCheck, witnessRow, leftRow,
    witnessMask, selectedMid, SourceForm.otherTent, SourceForm.supportMask,
    SelectedBranchData.cap, SourceForm.affine, gapLower, wholeBoxInfimum,
    rowCap, ownSlots, ownSlot, strictSquareGates, selectedWord, remainingWord,
    box, qLo, qHi, qPoint, witnessCode, witnessRange, witnessBuffer, ceiling,
    Fin.sum_univ_succ]

theorem witness_in_alternatives :
    witnessRow ∈ alternatives witnessRange witnessBuffer 3 witnessCode := by
  apply List.mem_flatMap.mpr
  refine ⟨witnessMask, ?_, ?_⟩
  · exact Finset.mem_toList.mpr (by
      norm_num [tentMasks, witnessMask, formRankEligible])
  · simp [screened, witness_lower_side, witness_source_check]

/-- A bounded finite source comparison, not a numerical integration or
    historical table replay. Each mask is checked against the literal
    original affine formulas on this one closed rational chamber. -/
theorem witness_dominates (c : SelectedBranchData)
    (hc : c ∈ alternatives witnessRange witnessBuffer 3 witnessCode) :
    c.cap = witnessRow.cap ∨
      0 < gapLower witnessRow.cap c.cap (box witnessRange witnessCode) := by
  obtain ⟨mask, hm, hside, _, _⟩ :=
    alternatives_source witnessRange witnessBuffer 3 witnessCode c hc
  fin_cases mask <;>
    norm_num [tentMasks, formRankEligible, lowerSide, leftRow, rightRow,
      selectedMid, witnessRow, witnessMask, maskNumber,
      SelectedBranchData.cap, SourceForm.affine, gapLower, wholeBoxInfimum,
      box, qLo, qHi, qPoint, witnessCode, witnessRange, ceiling,
      Fin.sum_univ_succ] at hm hside ⊢ <;> subst c <;> simp_all

theorem witness_not_base :
    ¬ stableBase (box witnessRange witnessCode) (initialRow witnessSeed)
      (alternatives witnessRange witnessBuffer 3 witnessCode) := by
  intro h
  rcases h witnessRow witness_in_alternatives with heq | hgap
  · have he := congrArg AffineBranch.constant heq
    norm_num [initialRow, witnessSeed, witnessRow, leftRow,
      SelectedBranchData.cap, SourceForm.affine] at he
  · norm_num [initialRow, witnessSeed, witnessRow, leftRow,
      SelectedBranchData.cap, SourceForm.affine, gapLower, wholeBoxInfimum,
      box, qLo, qHi, qPoint, witnessCode, witnessRange, ceiling,
      Fin.sum_univ_succ] at hgap

private theorem firstStable_exists {P : SelectedBranchData → Prop}
    (rows : List SelectedBranchData) (b : SelectedBranchData)
    (hb : b ∈ rows) (hP : P b) : ∃ c, firstStable P rows = some c := by
  induction rows with
  | nil => simp at hb
  | cons a as ih =>
      by_cases ha : P a
      · exact ⟨a, by simp [firstStable, ha]⟩
      · have hb' : b ∈ as := by
          rcases List.mem_cons.mp hb with rfl | hb'
          · exact (ha hP).elim
          · exact hb'
        obtain ⟨c,hc⟩ := ih hb'
        exact ⟨c, by simpa [firstStable,ha] using hc⟩

theorem witness_selected : ∃ c,
    select witnessRange (bank witnessRange 225 witnessBuffer witnessSeed)
      witnessBuffer 3 witnessCode = some c ∧ c.cap = witnessRow.cap := by
  have hbSign : 0 < gapLower witnessRow.cap (initialRow witnessSeed).cap
      (box witnessRange witnessCode) := by
    norm_num [initialRow, witnessSeed, witnessRow, leftRow,
      SelectedBranchData.cap, SourceForm.affine, gapLower, wholeBoxInfimum,
      box, qLo, qHi, qPoint, witnessCode, witnessRange, ceiling,
      Fin.sum_univ_succ]
  have hstable : stableAlternative witnessRange 3 witnessCode witnessBuffer
      (initialRow witnessSeed) (alternatives witnessRange witnessBuffer 3 witnessCode)
      witnessRow :=
    ⟨witness_source_check, Or.inr hbSign, fun c hc =>
      (witness_dominates c hc).imp Eq.symm id⟩
  obtain ⟨c,hc⟩ := firstStable_exists _ witnessRow witness_in_alternatives hstable
  have hs := firstStable_some hc
  have heq : c.cap = witnessRow.cap := by
    rcases witness_dominates c hs.1 with he | hbc
    · exact he
    · rcases hs.2.2.2 witnessRow witness_in_alternatives with he | hcb
      · exact he
      · have h1 := gapLower_le_eval_gap witnessRow.cap c.cap _ witnessPoint witness_in_box
        have h2 := gapLower_le_eval_gap c.cap witnessRow.cap _ witnessPoint witness_in_box
        have hbcR : (0:ℝ) < (gapLower witnessRow.cap c.cap (box witnessRange witnessCode):ℝ) :=
          by exact_mod_cast hbc
        have hcbR : (0:ℝ) < (gapLower c.cap witnessRow.cap (box witnessRange witnessCode):ℝ) :=
          by exact_mod_cast hcb
        linarith
  refine ⟨c, ?_, heq⟩
  simpa [select, bank, witness_prefix, witness_not_base, hc] using hc

/-- The concrete finite plan really freezes a nontrivial original tent
    cap. No successful-selection/plan premise is supplied to this theorem. -/
theorem witness_plan_fresh : ∃ argument,
    (plan witnessRange 225 witnessBuffer witnessSeed).choose 3 witnessCode =
      .fresh (589/1000) argument := by
  obtain ⟨c,hsel,hcap⟩ := witness_selected
  have hrow : rowCap witnessRange witnessCode witnessBuffer c = 589/1000 := by
    unfold rowCap
    rw [hcap]
    norm_num [witnessRow,leftRow,SelectedBranchData.cap,SourceForm.affine,
      wholeBoxInfimum,box,qLo,qHi,qPoint,witnessCode,witnessRange,
      witnessMask,witnessBuffer,ceiling,Fin.sum_univ_succ]
  have hcheck : freshCheck witnessRange 3 witnessCode witnessBuffer witnessSeed c := by
    rw [freshCheck,hrow]
    norm_num [witnessSeed,arrivalGate]
  refine ⟨c.argument, ?_⟩
  change checkedChoice witnessRange (bank witnessRange 225 witnessBuffer witnessSeed)
    witnessBuffer 3 (witnessSeed:ℝ) witnessCode = _
  have hchoice := checkedChoice_fresh witnessRange
    (bank witnessRange 225 witnessBuffer witnessSeed) witnessBuffer 3
    (witnessSeed:ℝ) witnessCode c (by simpa [witness_prefix] using hsel)
    (by simpa [witness_prefix] using hcheck)
  simpa [witness_prefix,hrow] using hchoice

theorem witness_original_history :
    2*(witnessPoint 0) < (witnessSeed:ℝ) ∧
      witnessPoint 0 + 3*witnessPoint 1 < (witnessSeed:ℝ) ∧
      (witnessSeed:ℝ) < 589/1000 ∧ (589/1000:ℝ) < 153/256 := by
  norm_num [witnessPoint,witnessSeed]

/-- This PARTICULAR concrete source has the strict analytic geometry of
    the original selected-subproduct criterion. No blanket licence for
    arbitrary positive/negative buffer or seed parameters is inferred. -/
theorem witness_strict_selected_interval (x : Fin 5 → ℝ)
    (hx : inBox (box witnessRange witnessCode) x) :
    (0:ℚ) < witnessBuffer ∧ (1/2:ℝ) < (witnessSeed:ℝ) ∧
      2*(589/1000:ℝ)-1 < x 0+x 1 ∧
      x 0+x 1 < actualSelectedSubproductUpper 1 (589/1000) := by
  have h0 := hx 0
  have h1 := hx 1
  norm_num [box,qLo,qHi,qPoint,witnessCode,witnessRange,ceiling] at h0 h1
  refine ⟨by norm_num [witnessBuffer], by norm_num [witnessSeed], ?_, ?_⟩
  · linarith
  · rw [actualSelectedSubproductUpper,lt_min_iff]
    constructor <;> linarith

theorem witness_point_full_selected_squares (x : Fin 5 → ℝ)
    (hx : inBox (box witnessRange witnessCode) x) :
    strictSquareGates (589/1000) 0 [x 0,x 1,x 2] ∧
      strictSquareGates (589/1000) (x 0+x 1) [x 2] := by
  have h0 := hx 0
  have h1 := hx 1
  have h2 := hx 2
  norm_num [box,qLo,qHi,qPoint,witnessCode,witnessRange,ceiling] at h0 h1 h2
  simp only [strictSquareGates,true_and,and_true]
  constructor
  · constructor
    · linarith
    · constructor <;> linarith
  · linarith

private theorem witness_code_tenth :
    exponentCode (1/100:ℝ) (59/250) 225 (1/10) = some ⟨90,by decide⟩ := by
  apply exponentCode_eq_of_cell (by norm_num)
  · norm_num
  · norm_num [exponentCell,logPrimeMeshPoint,logPrimeMeshStep]

private theorem witness_code_two_twentyfifths :
    exponentCode (1/100:ℝ) (59/250) 225 (2/25) = some ⟨70,by decide⟩ := by
  apply exponentCode_eq_of_cell (by norm_num)
  · norm_num
  · norm_num [exponentCell,logPrimeMeshPoint,logPrimeMeshStep]

private theorem witness_code_twentyfifth :
    exponentCode (1/100:ℝ) (59/250) 225 (1/25) = some ⟨30,by decide⟩ := by
  apply exponentCode_eq_of_cell (by norm_num)
  · norm_num
  · norm_num [exponentCell,logPrimeMeshPoint,logPrimeMeshStep]

/-- This is the actual physical-code decoder, not an independent label
    supplied by a caller. Half-open ownership at lower endpoints is kept. -/
theorem witness_actual_code :
    codeAt witnessRange 225 3 [witnessPoint 0,witnessPoint 1,witnessPoint 2] =
      witnessCode := by
  have htop : exponentCode (1/100:ℝ) (59/250) 225 (59/250) = none := by
    simp [exponentCode]
  funext i
  fin_cases i <;>
    simp [codeAt,incomingCode,physicalCode,marked,witnessRange,ceiling,
      witnessPoint,witnessCode,witness_code_tenth,witness_code_two_twentyfifths,
      witness_code_twentyfifth,htop]

/-- A true reached third step of the concrete plan. Its current test uses
    the preceding seed and the new cap is frozen only after that test.
    This does not assert an arithmetic prime tuple exists in the box. -/
theorem witness_actual_third_step :
    let P := plan witnessRange 225 witnessBuffer witnessSeed
    let H : Trace := ⟨[witnessPoint 0,witnessPoint 1],witnessSeed,[],true⟩
    (step P witnessRange.epsilon ceiling H (witnessPoint 2)).accepted = true ∧
      (step P witnessRange.epsilon ceiling H (witnessPoint 2)).cap = 589/1000 := by
  dsimp only
  let P := plan witnessRange 225 witnessBuffer witnessSeed
  let H : Trace := ⟨[witnessPoint 0,witnessPoint 1],witnessSeed,[],true⟩
  obtain ⟨argument,hfresh⟩ := witness_plan_fresh
  have hchoice : planChoice P witnessRange.epsilon ceiling
      [witnessPoint 0,witnessPoint 1,witnessPoint 2] =
        .fresh (589/1000) argument := by
    change (if (3:ℕ)=3 ∨ (3:ℕ)=4 ∨ (3:ℕ)=5 then
      incomingChoice P witnessRange.epsilon ceiling 3
        (marked [witnessPoint 0,witnessPoint 1,witnessPoint 2]) else .inherit 2) = _
    rw [if_pos (Or.inl rfl)]
    change P.choose 3
      (codeAt witnessRange 225 3 [witnessPoint 0,witnessPoint 1,witnessPoint 2]) = _
    rw [witness_actual_code]
    exact hfresh
  constructor
  · apply (step_accepted_iff P witnessRange.epsilon ceiling H (witnessPoint 2)).2
    exact ⟨rfl,by simp [H,admission]⟩
  · change (planChoice P witnessRange.epsilon ceiling
      [witnessPoint 0,witnessPoint 1,witnessPoint 2]).freeze (witnessSeed:ℝ) = _
    simp only [hchoice,CapChoice.freeze]

theorem witness_in_original_second_start :
    ∀ i : Fin 3, (1/100:ℝ) ≤ witnessPoint ⟨i.val,by omega⟩ ∧
      witnessPoint ⟨i.val,by omega⟩ < (19/125:ℝ) := by
  intro i
  fin_cases i <;> norm_num [witnessPoint]

/-- An entire half-open rational source chamber owns this SAME code. -/
theorem chamber_actual_code (x0 x1 x2 : ℝ)
    (h0 : x0 ∈ Set.Ico (1/10:ℝ) (101/1000))
    (h1 : x1 ∈ Set.Ico (2/25:ℝ) (81/1000))
    (h2 : x2 ∈ Set.Ico (1/25:ℝ) (41/1000)) :
    codeAt witnessRange 225 3 [x0,x1,x2] = witnessCode := by
  have hc0 : exponentCode (1/100:ℝ) (59/250) 225 x0 = some ⟨90,by decide⟩ := by
    apply exponentCode_eq_of_cell (by norm_num)
    · constructor <;> linarith [h0.1,h0.2]
    · convert h0 using 1 <;> norm_num [exponentCell,logPrimeMeshPoint,logPrimeMeshStep]
  have hc1 : exponentCode (1/100:ℝ) (59/250) 225 x1 = some ⟨70,by decide⟩ := by
    apply exponentCode_eq_of_cell (by norm_num)
    · constructor <;> linarith [h1.1,h1.2]
    · convert h1 using 1 <;> norm_num [exponentCell,logPrimeMeshPoint,logPrimeMeshStep]
  have hc2 : exponentCode (1/100:ℝ) (59/250) 225 x2 = some ⟨30,by decide⟩ := by
    apply exponentCode_eq_of_cell (by norm_num)
    · constructor <;> linarith [h2.1,h2.2]
    · convert h2 using 1 <;> norm_num [exponentCell,logPrimeMeshPoint,logPrimeMeshStep]
  have ht : exponentCode (1/100:ℝ) (59/250) 225 (59/250) = none := by
    simp [exponentCode]
  funext i
  fin_cases i <;>
    simp [codeAt,incomingCode,physicalCode,marked,witnessRange,ceiling,
      witnessCode,hc0,hc1,hc2,ht]

/-- Nonempty positive-width source histories, starting at the ordinary
    root, really reach the nontrivial tent action after their first two
    chronological tests. No admitted/retained/selected history is an input. -/
theorem chamber_full_run (x0 x1 x2 : ℝ)
    (h0 : x0 ∈ Set.Ico (1/10:ℝ) (101/1000))
    (h1 : x1 ∈ Set.Ico (2/25:ℝ) (81/1000))
    (h2 : x2 ∈ Set.Ico (1/25:ℝ) (41/1000)) :
    let P := plan witnessRange 225 witnessBuffer witnessSeed
    (run P witnessRange.epsilon ceiling (root witnessSeed) [x0,x1,x2]).accepted = true ∧
      (run P witnessRange.epsilon ceiling (root witnessSeed) [x0,x1,x2]).cap = 589/1000 := by
  dsimp only
  let P := plan witnessRange 225 witnessBuffer witnessSeed
  let H1 := step P witnessRange.epsilon ceiling (root witnessSeed) x0
  let H2 := step P witnessRange.epsilon ceiling H1 x1
  have hcap1 : H1.cap = (witnessSeed:ℝ) := by
    simp [H1,step,planChoice,root,CapChoice.freeze]
  have hcap2 : H2.cap = (witnessSeed:ℝ) := by
    simp [H2,H1,step,planChoice,root,CapChoice.freeze]
  have hword2 : H2.word = [x0,x1] := rfl
  have hacc1 : H1.accepted = true := by
    apply (step_accepted_iff P witnessRange.epsilon ceiling (root witnessSeed) x0).2
    refine ⟨rfl,?_⟩
    simp only [admission,root,List.length_nil,if_true]
    norm_num [witnessSeed]
    linarith [h0.2]
  have hacc2 : H2.accepted = true := by
    apply (step_accepted_iff P witnessRange.epsilon ceiling H1 x1).2
    refine ⟨hacc1,?_⟩
    change x0+3*x1 < H1.cap
    rw [hcap1]
    norm_num [witnessSeed]
    linarith [h0.2,h1.2]
  obtain ⟨argument,hfresh⟩ := witness_plan_fresh
  have hchoice : planChoice P witnessRange.epsilon ceiling [x0,x1,x2] =
      .fresh (589/1000) argument := by
    change (if (3:ℕ)=3 ∨ (3:ℕ)=4 ∨ (3:ℕ)=5 then
      incomingChoice P witnessRange.epsilon ceiling 3 (marked [x0,x1,x2])
      else .inherit 2) = _
    rw [if_pos (Or.inl rfl)]
    change P.choose 3 (codeAt witnessRange 225 3 [x0,x1,x2]) = _
    rw [chamber_actual_code x0 x1 x2 h0 h1 h2]
    exact hfresh
  change (step P witnessRange.epsilon ceiling H2 x2).accepted = true ∧
    (step P witnessRange.epsilon ceiling H2 x2).cap = _
  constructor
  · apply (step_accepted_iff P witnessRange.epsilon ceiling H2 x2).2
    exact ⟨hacc2,by simp [admission,hword2]⟩
  · change (planChoice P witnessRange.epsilon ceiling (H2.word++[x2])).freeze H2.cap = _
    rw [hword2,hcap2]
    simpa [hchoice,CapChoice.freeze]

end
end ImbalancedChen.P2OriginalCanonicalPairTentBank
