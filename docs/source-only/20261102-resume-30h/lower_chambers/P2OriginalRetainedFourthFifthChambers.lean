import ImbalancedChen.P2OriginalActiveTentSelectorApproximation

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Two retained open original source chambers, not supplied successful checks.
Rank four selects {0,1,3}, rank five selects {0,1,3,4}; in BOTH chambers
the remaining selected-complement word is the nonempty original slot [2].
All full squares, that complement square, the lower tent side and every
competing rank-eligible mask are proved from rational coordinate bounds.
The final theorems use cap3/cap4 of the independent computed finite policy,
and output its actual cap4/cap5 approximation. The preceding one-sided
parent comparison is explicitly an induction hypothesis. These two source
components do not constitute full W/adopted-bank coverage.
-/

namespace ImbalancedChen.P2OriginalRetainedFourthFifthChambers

noncomputable section
open scoped Classical BigOperators
open Set
open P2EnhancedLowerPhysicalNode P2LowerCapPlanIntegerRetention
open P2OriginalLowerSelectedCapConstructor (Code prefixCode strictSquareGates)
open P2OriginalLowerAffineTieSelector P2OriginalLowerBufferedAffineBoxes
open P2OriginalLowerWholeBoxBranchSelect
open P2OriginalFiniteTentBankSelectorMargins (tentMasks)
open P2OriginalPairSourceReceiver P2OriginalCanonicalPairTentBank
open P2OriginalIdealTentCanonicalScreen P2OriginalCanonicalTentFrozenChambers
open P2OriginalRetainedTentCompactMargin
open P2OriginalActiveTentSelectorApproximation

def mask4 : Finset (Fin 5) := {0,1,3}
def mask5 : Finset (Fin 5) := {0,1,3,4}
def center4 : Fin 5 → ℝ := ![2/25,3/40,1/20,1/25,59/250]
def center5 : Fin 5 → ℝ := ![2/25,7/100,1/20,3/100,3/200]
def chamber4 (x : Fin 5 → ℝ) : Prop :=
  ∀ i : Fin 5, i.val < 4 → |x i - center4 i| < 1/100000
def chamber5 (x : Fin 5 → ℝ) : Prop :=
  ∀ i : Fin 5, |x i - center5 i| < 1/100000

theorem center4_mem : chamber4 center4 := by
  intro i hi
  simp
theorem center5_mem : chamber5 center5 := by
  intro i
  simp

theorem mask4_original : mask4 ∈ tentMasks 4 := by
  norm_num [tentMasks, formRankEligible, mask4]
theorem mask5_original : mask5 ∈ tentMasks 5 := by
  norm_num [tentMasks, formRankEligible, mask5]

-- These are exactly the two original gate systems, including the selected
-- initial sum. Slot 2 has not been dropped or replaced by a full-word test.
theorem fourth_source_margin (x : Fin 5 → ℝ) (hx : chamber4 x) :
    x ∈ region 4 mask4 false (1/10000 : ℝ) ∧
      (597/1000 : ℝ) < endpoint mask4 false x ∧
      endpoint mask4 false x < (153/256 : ℝ) ∧
      x 0+x 1+x 2+3*x 3+(1/10000 : ℝ) < (11/20 : ℝ) := by
  have h0 := abs_lt.mp (hx 0 (by norm_num))
  have h1 := abs_lt.mp (hx 1 (by norm_num))
  have h2 := abs_lt.mp (hx 2 (by norm_num))
  have h3 := abs_lt.mp (hx 3 (by norm_num))
  norm_num [center4] at h0 h1 h2 h3
  norm_num [region, endpoint, tentForm, mask4, SourceForm.affine,
    AffineBranch.eval, fullFunctions, selectedFunctions, remainingFunctions,
    indices, evaluate, strictSquareGates, Fin.sum_univ_succ]
  repeat' constructor <;> linarith [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2]

theorem fifth_source_margin (x : Fin 5 → ℝ) (hx : chamber5 x) :
    x ∈ region 5 mask5 false (1/10000 : ℝ) ∧
      (597/1000 : ℝ) < endpoint mask5 false x ∧
      endpoint mask5 false x < (153/256 : ℝ) := by
  have h0 := abs_lt.mp (hx 0)
  have h1 := abs_lt.mp (hx 1)
  have h2 := abs_lt.mp (hx 2)
  have h3 := abs_lt.mp (hx 3)
  have h4 := abs_lt.mp (hx 4)
  norm_num [center5] at h0 h1 h2 h3 h4
  norm_num [region, endpoint, tentForm, mask5, SourceForm.affine,
    AffineBranch.eval, fullFunctions, selectedFunctions, remainingFunctions,
    indices, evaluate, strictSquareGates, Fin.sum_univ_succ]
  repeat' constructor <;>
    linarith [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2]

-- Finite structural mask cases are written as proof terms and are NOT
-- run here. The comparisons are with all original masks, before screening.
theorem fourth_original_winner_margin (x : Fin 5 → ℝ) (hx : chamber4 x)
    (J : Finset (Fin 5)) (hJ : J ∈ tentMasks 4) (hne : J ≠ mask4) :
    (1/10000 : ℝ) ≤ endpoint mask4 false x - VariableEnvelope.v (∑ i ∈ J, x i) := by
  have h0 := abs_lt.mp (hx 0 (by norm_num))
  have h1 := abs_lt.mp (hx 1 (by norm_num))
  have h2 := abs_lt.mp (hx 2 (by norm_num))
  have h3 := abs_lt.mp (hx 3 (by norm_num))
  norm_num [center4] at h0 h1 h2 h3
  have hA : VariableEnvelope.v (∑ i ∈ J, x i) ≤ (1 + ∑ i ∈ J, x i)/2 := by
    rw [VariableEnvelope.v_eq_min]
    exact min_le_left _ _
  have hC : VariableEnvelope.v (∑ i ∈ J, x i) ≤ 57/64 - (3/2)*(∑ i ∈ J, x i) := by
    rw [VariableEnvelope.v_eq_min]
    exact min_le_right _ _
  fin_cases J <;>
    norm_num [tentMasks, formRankEligible, mask4, endpoint, tentForm,
      SourceForm.affine, AffineBranch.eval, Fin.sum_univ_succ] at hJ hne hA hC ⊢ <;>
    linarith [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2]

theorem fifth_original_winner_margin (x : Fin 5 → ℝ) (hx : chamber5 x)
    (J : Finset (Fin 5)) (hJ : J ∈ tentMasks 5) (hne : J ≠ mask5) :
    (1/10000 : ℝ) ≤ endpoint mask5 false x - VariableEnvelope.v (∑ i ∈ J, x i) := by
  have h0 := abs_lt.mp (hx 0)
  have h1 := abs_lt.mp (hx 1)
  have h2 := abs_lt.mp (hx 2)
  have h3 := abs_lt.mp (hx 3)
  have h4 := abs_lt.mp (hx 4)
  norm_num [center5] at h0 h1 h2 h3 h4
  have hA : VariableEnvelope.v (∑ i ∈ J, x i) ≤ (1 + ∑ i ∈ J, x i)/2 := by
    rw [VariableEnvelope.v_eq_min]
    exact min_le_left _ _
  have hC : VariableEnvelope.v (∑ i ∈ J, x i) ≤ 57/64 - (3/2)*(∑ i ∈ J, x i) := by
    rw [VariableEnvelope.v_eq_min]
    exact min_le_right _ _
  fin_cases J <;>
    norm_num [tentMasks, formRankEligible, mask5, endpoint, tentForm,
      SourceForm.affine, AffineBranch.eval, Fin.sum_univ_succ] at hJ hne hA hC ⊢ <;>
    linarith [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2]

theorem actualCode_prefix (R : PairRange) (mesh : ℕ) (rank : Fin 6) (x : Fin 5 → ℝ) :
    prefixCode rank.val (actualCode R mesh rank x) = actualCode R mesh rank x := by
  funext i
  by_cases hi : i.val < rank.val <;> simp [prefixCode, actualCode_at, hi]

-- Rank-four padding only embeds the prefix. It places no restriction on
-- later physical primes. Both gate systems use the same actual Code bits.
theorem fourth_screen_and_selection (R : PairRange) (mesh : ℕ)
    (buffer floor : ℚ) (hb : 0 ≤ buffer) (hfloor : (floor : ℝ) ≤ 59/100)
    (x : Fin 5 → ℝ) (hx : chamber4 x)
    (hrange : ∀ i, x i ∈ Icc (R.epsilon : ℝ) (ceiling : ℝ))
    (hmesh : 16 * logPrimeMeshStep (R.epsilon : ℝ) (ceiling : ℝ) mesh + buffer < 1/10000) :
    let code := actualCode R mesh 4 x
    select R (bank R mesh buffer floor) buffer 4 code = some (chosenRow R code mask4 false) ∧
      sourceCheck R 4 code buffer (chosenRow R code mask4 false) := by
  dsimp only
  let X := actualPoint 4 x
  have hX : chamber4 X := by
    intro i hi
    simpa [X, actualPoint, hi] using hx i hi
  have hg := fourth_source_margin X hX
  have hw := actual_point_words R mesh 4 mask4 X
  have hcode : actualCode R mesh 4 X = actualCode R mesh 4 x := by
    funext i
    by_cases hi : i.val < 4 <;> simp [actualCode_at, X, actualPoint, hi]
  rw [hcode] at hw
  apply original_strict_winner_selected R mesh 4 _ (actualCode_prefix R mesh 4 x)
    X (actualCode_point_in_box R mesh 4 x hrange) mask4 mask4_original false buffer floor hb
    (1/10000) (by norm_num) hmesh
  · simpa [otherRow, chosen_endpoint] using hg.1.1.le
  · simpa [chosen_endpoint, hw.1] using hg.1.2.1
  · simpa [chosen_endpoint, hw.2.1, hw.2.2] using hg.1.2.2
  · rw [chosen_endpoint]
    linarith [hg.2.1]
  · intro J hJ hne
    simpa [chosen_endpoint] using fourth_original_winner_margin X hX J hJ hne

-- This eliminates G's unconnected candidate at rank four. The only
-- preceding-rank approximation premise is the actual cap3 error; no cap4
-- estimate, selected row, full/selected gate or successful check is input.
theorem fourth_actual_cap_approximation (R : PairRange) (mesh : ℕ)
    (buffer floor : ℚ) (hb : 0 ≤ buffer) (hfloor : (floor : ℝ) ≤ 59/100)
    (root : ℝ) (x : Fin 5 → ℝ) (hx : chamber4 x)
    (hrange : ∀ i, x i ∈ Icc (R.epsilon : ℝ) (ceiling : ℝ))
    (C3 : ℝ) (hClo : 11/20 ≤ C3) (hChi : C3 ≤ 59/100)
    (hparent : cap3 R (bank R mesh buffer floor) buffer root (actualCode R mesh 4 x) ≤ C3)
    (herror : C3 - cap3 R (bank R mesh buffer floor) buffer root
      (actualCode R mesh 4 x) ≤ 1/1000)
    (hmesh : 16 * logPrimeMeshStep (R.epsilon : ℝ) (ceiling : ℝ) mesh + buffer < 1/10000) :
    let code := actualCode R mesh 4 x
    cap4 R (bank R mesh buffer floor) buffer root code =
        (rowCap R code buffer (chosenRow R code mask4 false) : ℝ) ∧
      0 ≤ endpoint mask4 false x - cap4 R (bank R mesh buffer floor) buffer root code ∧
      endpoint mask4 false x - cap4 R (bank R mesh buffer floor) buffer root code ≤
        (15/2 : ℝ) * logPrimeMeshStep (R.epsilon : ℝ) (ceiling : ℝ) mesh + buffer := by
  dsimp only
  let code := actualCode R mesh 4 x
  let X := actualPoint 4 x
  have hX : chamber4 X := by
    intro i hi
    simpa [X, actualPoint, hi] using hx i hi
  have hg := fourth_source_margin X hX
  have he : endpoint mask4 false X = endpoint mask4 false x := by
    simp [endpoint, tentForm, mask4, SourceForm.affine, AffineBranch.eval,
      Fin.sum_univ_succ, X, actualPoint]
  have hs := fourth_screen_and_selection R mesh buffer floor hb hfloor x hx hrange hmesh
  have hcube : X 0+X 1+X 2+3*X 3+(1/10000 : ℝ) ≤
      cap3 R (bank R mesh buffer floor) buffer root code := by
    have h0 := abs_lt.mp (hx 0 (by norm_num))
    have h1 := abs_lt.mp (hx 1 (by norm_num))
    have h2 := abs_lt.mp (hx 2 (by norm_num))
    have h3 := abs_lt.mp (hx 3 (by norm_num))
    norm_num [center4] at h0 h1 h2 h3
    simp only [X, actualPoint]
    norm_num
    dsimp [code] at *
    linarith [h0.2,h1.2,h2.2,h3.2]
  have hf := original_actual_parent_fresh R code 4 X
    (actualCode_point_in_box R mesh 4 x hrange) (chosenRow R code mask4 false)
    buffer hb (1/10000) hmesh
    (cap3 R (bank R mesh buffer floor) buffer root code)
    (by rw [chosen_endpoint]; dsimp [code] at *; linarith [hg.2.1])
    (by rw [chosen_endpoint]; exact hg.2.2.1.le) (fun _ => hcube)
  have hc : cap4 R (bank R mesh buffer floor) buffer root code =
      (rowCap R code buffer (chosenRow R code mask4 false) : ℝ) := by
    simp [cap4, checkedCap, checkedChoice, actualCode_prefix, hs.1, hf, CapChoice.freeze, code]
  refine ⟨hc, ?_⟩
  rw [hc, ← he, ← chosen_endpoint R code mask4 false X]
  exact P2OriginalFrozenParentApproximationStep.candidate_cap_error R code X
    (actualCode_point_in_box R mesh 4 x hrange) _ buffer hb

-- Fifth reads the actual fourth state, including inherited states. There
-- is no fifth arrival cube and no equality between finite and ideal C4.
theorem fifth_actual_cap_approximation (R : PairRange) (mesh : ℕ)
    (buffer floor : ℚ) (hb : 0 ≤ buffer) (hfloor : (floor : ℝ) ≤ 591/1000)
    (root : ℝ) (x : Fin 5 → ℝ) (hx : chamber5 x)
    (hrange : ∀ i, x i ∈ Icc (R.epsilon : ℝ) (ceiling : ℝ))
    (C4 : ℝ) (hC4 : C4 ≤ 591/1000)
    (hparent : cap4 R (bank R mesh buffer floor) buffer root (actualCode R mesh 5 x) ≤ C4)
    (hmesh : 16 * logPrimeMeshStep (R.epsilon : ℝ) (ceiling : ℝ) mesh + buffer < 1/10000) :
    let code := actualCode R mesh 5 x
    cap5 R (bank R mesh buffer floor) buffer root code =
        (rowCap R code buffer (chosenRow R code mask5 false) : ℝ) ∧
      0 ≤ endpoint mask5 false x - cap5 R (bank R mesh buffer floor) buffer root code ∧
      endpoint mask5 false x - cap5 R (bank R mesh buffer floor) buffer root code ≤
        (15/2 : ℝ) * logPrimeMeshStep (R.epsilon : ℝ) (ceiling : ℝ) mesh + buffer := by
  dsimp only
  have hg := fifth_source_margin x hx
  have hw := actual_point_words R mesh 5 mask5 x
  have hpoint : actualPoint 5 x = x := by
    funext i
    simp [actualPoint, i.isLt]
  have hbox : inBox (box R (actualCode R mesh 5 x)) x := by
    simpa [hpoint] using actualCode_point_in_box R mesh 5 x hrange
  have h := checkedCap_eq_and_error_of_original_winner R mesh 5 _
    (actualCode_prefix R mesh 5 x) x hbox mask5 mask5_original false buffer floor hb
    (1/10000) (by norm_num) hmesh
    (by simpa [otherRow, chosen_endpoint] using hg.1.1.le)
    (by simpa [chosen_endpoint, hw.1] using hg.1.2.1)
    (by simpa [chosen_endpoint, hw.2.1, hw.2.2] using hg.1.2.2)
    (by rw [chosen_endpoint]; linarith [hg.2.1])
    (fun J hJ hne => by
      simpa [chosen_endpoint] using fifth_original_winner_margin x hx J hJ hne)
    (cap4 R (bank R mesh buffer floor) buffer root (actualCode R mesh 5 x))
    (by rw [chosen_endpoint]; linarith [hg.2.1])
    (by rw [chosen_endpoint]; exact hg.2.2.le)
    (by intro hbad; norm_num at hbad)
  simpa only [cap5, chosen_endpoint] using h

-- Explicit original physical run consumer. The full five-prime prefix,
-- real incoming root and unchanged pairPlan appear on the left-hand side.
theorem fifth_run_cap_approximation (R : PairRange) (mesh : ℕ)
    (buffer floor : ℚ) (hb : 0 ≤ buffer) (hfloor : (floor : ℝ) ≤ 591/1000)
    (root : ℝ) (x : Fin 5 → ℝ) (hx : chamber5 x)
    (hrange : ∀ i, x i ∈ Icc (R.epsilon : ℝ) (ceiling : ℝ))
    (C4 : ℝ) (hC4 : C4 ≤ 591/1000)
    (hparent : cap4 R (bank R mesh buffer floor) buffer root (actualCode R mesh 5 x) ≤ C4)
    (hmesh : 16 * logPrimeMeshStep (R.epsilon : ℝ) (ceiling : ℝ) mesh + buffer < 1/10000) :
    let H := run (pairPlan R (bank R mesh buffer floor) buffer root) R.epsilon ceiling
      ⟨[x 0,x 1],root,[],true⟩ [x 2,x 3,x 4]
    0 ≤ endpoint mask5 false x - H.cap ∧
      endpoint mask5 false x - H.cap ≤
        (15/2 : ℝ) * logPrimeMeshStep (R.epsilon : ℝ) (ceiling : ℝ) mesh + buffer := by
  dsimp only
  rw [pair_run_three_cap]
  exact (fifth_actual_cap_approximation R mesh buffer floor hb hfloor root x hx hrange
    C4 hC4 hparent hmesh).2

-- The word is actually retained by the unchanged warm own-lower trace.
-- The sole even arrival among these three extensions is paid at H3.cap;
-- monotonicity of the computed third choice, rather than an ideal parent,
-- supplies its lower bound. Initial pair acceptance is part of the warm
-- input state and is still owned by the original root-provenance supplier.
theorem fifth_chamber_warm_retained (R : PairRange) (mesh : ℕ)
    (buffer floor : ℚ) (root : ℝ) (hroot : 11/20 ≤ root)
    (x : Fin 5 → ℝ) (hx : chamber5 x) :
    (run (pairPlan R (bank R mesh buffer floor) buffer root) R.epsilon ceiling
      ⟨[x 0,x 1],root,[],true⟩ [x 2,x 3,x 4]).accepted = true := by
  let P := pairPlan R (bank R mesh buffer floor) buffer root
  let H2 : Trace := ⟨[x 0,x 1],root,[],true⟩
  let H3 := step P R.epsilon ceiling H2 (x 2)
  let H4 := step P R.epsilon ceiling H3 (x 3)
  let H5 := step P R.epsilon ceiling H4 (x 4)
  have hcap : root ≤ H3.cap := by
    have h := checked_cap_mono R mesh buffer floor 3
      (codeAt R mesh 3 [x 0,x 1,x 2]) root
    simpa [H3,H2,P,step,planChoice,incomingChoice,pairPlan,codeAt,checkedCap] using h
  have hw3 : H3.word = [x 0,x 1,x 2] := by simp [H3,H2,step]
  have ha3 : admission H2 (x 2) := by simp [admission,H2]
  have ha4 : admission H3 (x 3) := by
    have h0 := (abs_lt.mp (hx 0)).2
    have h1 := (abs_lt.mp (hx 1)).2
    have h2 := (abs_lt.mp (hx 2)).2
    have h3 := (abs_lt.mp (hx 3)).2
    norm_num [center5] at h0 h1 h2 h3
    simp only [admission,hw3,List.length_cons,List.length_nil,List.sum_cons,List.sum_nil]
    norm_num
    linarith
  have ha5 : admission H4 (x 4) := by simp [admission,H4,H3,H2,step]
  have h3 : H3.accepted = true :=
    (step_accepted_iff P R.epsilon ceiling H2 (x 2)).mpr ⟨rfl,ha3⟩
  have h4 : H4.accepted = true :=
    (step_accepted_iff P R.epsilon ceiling H3 (x 3)).mpr ⟨h3,ha4⟩
  have h5 : H5.accepted = true :=
    (step_accepted_iff P R.epsilon ceiling H4 (x 4)).mpr ⟨h4,ha5⟩
  exact h5

theorem fifth_retained_run_approximation (R : PairRange) (mesh : ℕ)
    (buffer floor : ℚ) (hb : 0 ≤ buffer) (hfloor : (floor : ℝ) ≤ 591/1000)
    (root : ℝ) (hroot : 11/20 ≤ root) (x : Fin 5 → ℝ) (hx : chamber5 x)
    (hrange : ∀ i, x i ∈ Icc (R.epsilon : ℝ) (ceiling : ℝ))
    (C4 : ℝ) (hC4 : C4 ≤ 591/1000)
    (hparent : cap4 R (bank R mesh buffer floor) buffer root (actualCode R mesh 5 x) ≤ C4)
    (hmesh : 16 * logPrimeMeshStep (R.epsilon : ℝ) (ceiling : ℝ) mesh + buffer < 1/10000) :
    let H := run (pairPlan R (bank R mesh buffer floor) buffer root) R.epsilon ceiling
      ⟨[x 0,x 1],root,[],true⟩ [x 2,x 3,x 4]
    H.accepted = true ∧ 0 ≤ endpoint mask5 false x - H.cap ∧
      endpoint mask5 false x - H.cap ≤
        (15/2 : ℝ) * logPrimeMeshStep (R.epsilon : ℝ) (ceiling : ℝ) mesh + buffer := by
  exact ⟨fifth_chamber_warm_retained R mesh buffer floor root hroot x hx,
    fifth_run_cap_approximation R mesh buffer floor hb hfloor root x hx hrange C4 hC4 hparent hmesh⟩

-- One pre-N mesh and one buffer pay BOTH local active source components
-- to any requested accuracy. The former G candidate-only error is now
-- applied to their actual cap4/cap5 conclusions. Parent induction bounds
-- remain visible, quantified after the common mesh choice.
theorem both_chambers_one_accuracy_mesh (R : PairRange) (eta : ℝ) (heta : 0 < eta) :
    ∃ buffer : ℚ, 0 < buffer ∧ ∃ M : ℕ, ∀ mesh : ℕ, M ≤ mesh →
      (∀ (floor : ℚ), (floor : ℝ) ≤ 59/100 →
        ∀ (root : ℝ) (x : Fin 5 → ℝ), chamber4 x →
        (∀ i, x i ∈ Icc (R.epsilon : ℝ) (ceiling : ℝ)) →
        ∀ C3 : ℝ, 11/20 ≤ C3 → C3 ≤ 59/100 →
        cap3 R (bank R mesh buffer floor) buffer root (actualCode R mesh 4 x) ≤ C3 →
        C3 - cap3 R (bank R mesh buffer floor) buffer root (actualCode R mesh 4 x) ≤ 1/1000 →
        0 ≤ endpoint mask4 false x - cap4 R (bank R mesh buffer floor) buffer root
          (actualCode R mesh 4 x) ∧
        endpoint mask4 false x - cap4 R (bank R mesh buffer floor) buffer root
          (actualCode R mesh 4 x) < eta) ∧
      (∀ (floor : ℚ), (floor : ℝ) ≤ 591/1000 →
        ∀ (root : ℝ) (x : Fin 5 → ℝ), chamber5 x →
        (∀ i, x i ∈ Icc (R.epsilon : ℝ) (ceiling : ℝ)) →
        ∀ C4 : ℝ, C4 ≤ 591/1000 →
        cap4 R (bank R mesh buffer floor) buffer root (actualCode R mesh 5 x) ≤ C4 →
        0 ≤ endpoint mask5 false x - cap5 R (bank R mesh buffer floor) buffer root
          (actualCode R mesh 5 x) ∧
        endpoint mask5 false x - cap5 R (bank R mesh buffer floor) buffer root
          (actualCode R mesh 5 x) < eta) := by
  have hmargin : 0 < min (1/10000 : ℝ) eta := lt_min (by norm_num) heta
  obtain ⟨buffer, hb0, hbmargin⟩ := exists_rat_btwn hmargin
  have hb : (0 : ℚ) < buffer := by exact_mod_cast hb0
  obtain ⟨M,hM⟩ := exists_uniform_canonical_tent_mesh R buffer hb.le _ hbmargin
  refine ⟨buffer,hb,M,?_⟩
  intro mesh hm
  have hstep := hM mesh hm
  have hsource : 16 * logPrimeMeshStep (R.epsilon : ℝ) (ceiling : ℝ) mesh + buffer <
      (1/10000 : ℝ) := hstep.trans_le (min_le_left _ _)
  have herr : (15/2 : ℝ) * logPrimeMeshStep (R.epsilon : ℝ) (ceiling : ℝ) mesh + buffer < eta := by
    have hrange : (R.epsilon : ℝ) < (ceiling : ℝ) := by
      exact_mod_cast lt_trans R.epsilon_lt_a
        (by norm_num [ceiling] : (417 : ℚ)/5000 < ceiling)
    have hh := (logPrimeMeshStep_pos hrange mesh).le
    have he := hstep.trans_le (min_le_right _ _)
    linarith
  constructor
  · intro floor hfloor root x hx hrange C3 hClo hChi hparent herror
    have h := (fourth_actual_cap_approximation R mesh buffer floor hb.le hfloor root x hx
      hrange C3 hClo hChi hparent herror hsource).2
    exact ⟨h.1, h.2.trans_lt herr⟩
  · intro floor hfloor root x hx hrange C4 hC4 hparent
    have h := (fifth_actual_cap_approximation R mesh buffer floor hb.le hfloor root x hx
      hrange C4 hC4 hparent hsource).2
    exact ⟨h.1, h.2.trans_lt herr⟩

end
end ImbalancedChen.P2OriginalRetainedFourthFifthChambers
