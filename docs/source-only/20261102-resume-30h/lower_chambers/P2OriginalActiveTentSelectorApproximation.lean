import ImbalancedChen.P2OriginalFrozenParentApproximationStep

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The missing active step after G: original strict point gates and comparisons
with the ORIGINAL finite mask alphabet imply the COMPUTED selector result.
The selected candidate then passes the retest at the TRUE frozen parent,
and the cap error is an error of checkedCap, rather than a candidate which
might never be used. This is an exact source theorem for the independently
defined canonical tent bank. It does not identify that subbank with the
full W/adopted lower policy.
-/

namespace ImbalancedChen.P2OriginalActiveTentSelectorApproximation

noncomputable section
open scoped Classical BigOperators
open P2EnhancedLowerPhysicalNode P2LowerCapPlanIntegerRetention
open P2OriginalLowerSelectedCapConstructor (Code prefixCode strictSquareGates)
open P2OriginalLowerAffineTieSelector P2OriginalLowerBufferedAffineBoxes
open P2OriginalLowerWholeBoxBranchSelect
open P2OriginalLowerFiniteAffineMeshWidth (slopeNorm)
open P2OriginalUniformMixedTentWChoice (source_slopeNorm_le source_difference_norm_le)
open P2OriginalFiniteTentBankSelectorMargins (tentMasks)
open P2OriginalPairSourceReceiver P2OriginalCanonicalPairTentBank
open P2OriginalIdealTentCanonicalScreen P2OriginalCanonicalTentFrozenChambers
open P2OriginalFrozenParentApproximationStep

private theorem firstStable_unique {rows : List SelectedBranchData}
    {P : SelectedBranchData → Prop} {b : SelectedBranchData}
    (hb : b ∈ rows) (hPb : P b) (hu : ∀ c ∈ rows, P c → c = b) :
    firstStable P rows = some b := by
  induction rows with
  | nil => cases hb
  | cons c cs ih =>
      by_cases hc : P c
      · have hcb := hu c List.mem_cons_self hc
        subst c
        simp [firstStable, hPb]
      · have hbt : b ∈ cs := by
          rcases List.mem_cons.mp hb with heq | ht
          · subst c
            exact (hc hPb).elim
          · exact ht
        simpa [firstStable, hc] using
          ih hbt (fun d hd hPd => hu d (List.mem_cons_of_mem _ hd) hPd)

private theorem range_lt (R : PairRange) : (R.epsilon : ℝ) < (ceiling : ℝ) := by
  exact_mod_cast lt_trans R.epsilon_lt_a
    (by norm_num [ceiling] : (417 : ℚ) / 5000 < ceiling)

private theorem qPoint_cast (R : PairRange) (mesh j : ℕ) :
    (qPoint R mesh j : ℝ) = logPrimeMeshPoint (R.epsilon : ℝ) (ceiling : ℝ) mesh j := by
  unfold qPoint logPrimeMeshPoint logPrimeMeshStep
  push_cast
  ring

theorem original_upper_endpoint_step (R : PairRange) {mesh : ℕ}
    (code : Code mesh) (x : Fin 5 → ℝ) (hx : inBox (box R code) x) (i : Fin 5) :
    (qHi R mesh (code i).1 : ℝ) ≤
      x i + logPrimeMeshStep (R.epsilon : ℝ) (ceiling : ℝ) mesh := by
  have hh := (logPrimeMeshStep_pos (range_lt R) mesh).le
  have hw : ((box R code).hi i : ℝ) - (box R code).lo i ≤
      logPrimeMeshStep (R.epsilon : ℝ) (ceiling : ℝ) mesh := by
    cases hc : (code i).1 with
    | none => simpa [box, qLo, qHi, hc] using hh
    | some j =>
        simp only [box, hc, qLo, qHi, qPoint_cast, logPrimeMeshPoint_succ]
        linarith
  have hl := (hx i).1
  dsimp [box] at hl hw
  linarith

-- Public source-local retest: reuse G's candidate error, then pay the
-- six-coordinate-weight fourth cube by the same actual mesh. The older F
-- generic retest lemma is private and is deliberately not referenced.
theorem original_actual_parent_fresh (R : PairRange) {mesh : ℕ}
    (code : Code mesh) (rank : Fin 6) (x : Fin 5 → ℝ)
    (hx : inBox (box R code) x) (b : SelectedBranchData)
    (buffer : ℚ) (hb : 0 ≤ buffer) (m : ℝ)
    (hmesh : 16 * logPrimeMeshStep (R.epsilon : ℝ) (ceiling : ℝ) mesh + buffer < m)
    (parent : ℝ) (hparent : parent + m ≤ b.cap.eval x)
    (htop : b.cap.eval x ≤ (153 : ℝ)/256)
    (harrival : rank.val = 4 → x 0+x 1+x 2+3*x 3+m ≤ parent) :
    freshCheck R rank code buffer parent b := by
  have hh := (logPrimeMeshStep_pos (range_lt R) mesh).le
  have hbR : (0 : ℝ) ≤ buffer := by exact_mod_cast hb
  have hloss := candidate_cap_error R code x hx b buffer hb
  refine ⟨by linarith, by linarith, ?_⟩
  unfold arrivalGate
  split_ifs with hr
  · have hc := harrival hr
    have h0 := original_upper_endpoint_step R code x hx 0
    have h1 := original_upper_endpoint_step R code x hx 1
    have h2 := original_upper_endpoint_step R code x hx 2
    have h3 := original_upper_endpoint_step R code x hx 3
    linarith
  · trivial

-- The same PairRange physical box used by the receiver, including its
-- original 59/250 external-prime ceiling, pays the affine comparison.
theorem positive_gap_from_original_point (R : PairRange) {mesh : ℕ}
    (code : Code mesh) (x : Fin 5 → ℝ) (hx : inBox (box R code) x)
    (a b : AffineBranch 5) (m : ℝ)
    (hnorm : slopeNorm (fun i => a.slope i - b.slope i) ≤ 15)
    (hpoint : m ≤ a.eval x - b.eval x)
    (hmesh : 15 * logPrimeMeshStep (R.epsilon : ℝ) (ceiling : ℝ) mesh < m) :
    0 < gapLower a b (box R code) := by
  have hh := (logPrimeMeshStep_pos (range_lt R) mesh).le
  have hnorm' := mul_le_mul_of_nonneg_right hnorm hh
  have hloss := ideal_minus_boxInf_le_step R code x hx
    (a.constant - b.constant) (fun i => a.slope i - b.slope i)
  have heval : affineValue (a.constant - b.constant)
      (fun i => a.slope i - b.slope i) x = a.eval x - b.eval x := by
    simp [affineValue, AffineBranch.eval, Rat.cast_sub, sub_mul, Finset.sum_sub_distrib]
    ring
  rw [heval] at hloss
  have hpos : (0 : ℝ) < gapLower a b (box R code) := by
    change (0 : ℝ) < (wholeBoxInfimum (a.constant - b.constant)
      (fun i => a.slope i - b.slope i) (box R code) : ℝ)
    linarith
  exact_mod_cast hpos

-- No successful screen, membership, whole-box dominance, or selector
-- equation is assumed. The comparisons range over the original eligible
-- masks, before any screening. These are strict retained winner chambers;
-- crossing and nonidentical tie walls remain outside this local theorem.
theorem original_strict_winner_selected (R : PairRange) (mesh : ℕ)
    (rank : Fin 6) (code : Code mesh) (hcanon : prefixCode rank.val code = code)
    (x : Fin 5 → ℝ) (hx : inBox (box R code) x)
    (mask : Finset (Fin 5)) (hm : mask ∈ tentMasks rank) (right : Bool)
    (buffer floor : ℚ) (hb : 0 ≤ buffer) (m : ℝ) (hm0 : 0 < m)
    (hmesh : 16 * logPrimeMeshStep (R.epsilon : ℝ) (ceiling : ℝ) mesh + buffer < m)
    (hside : m ≤ (otherRow R code mask right).cap.eval x -
      (chosenRow R code mask right).cap.eval x)
    (hfull : strictSquareGates ((chosenRow R code mask right).cap.eval x - m) 0
      ((pointSlots rank code mask x).map Slot.exponent))
    (hselected : strictSquareGates ((chosenRow R code mask right).cap.eval x - m)
      (selectedWord (pointSlots rank code mask x)).sum
      (remainingWord (pointSlots rank code mask x)))
    (hfloor : (floor : ℝ) + m ≤ (chosenRow R code mask right).cap.eval x)
    (hwinner : ∀ J ∈ tentMasks rank, J ≠ mask →
      m ≤ (chosenRow R code mask right).cap.eval x - VariableEnvelope.v (∑ i ∈ J, x i)) :
    select R (bank R mesh buffer floor) buffer rank code =
      some (chosenRow R code mask right) ∧
      sourceCheck R rank code buffer (chosenRow R code mask right) := by
  let b := chosenRow R code mask right
  let rows := alternatives R buffer rank code
  let base := initialRow floor
  have hscreen := ideal_tent_enters_concrete_screen R code rank x hx mask hm
    right buffer hb m hm0 hmesh hside hfull hselected
  have hmem : b ∈ rows := every_screened_original_action_occurs R mesh buffer floor
    rank code mask hm b hscreen.1 hscreen.2
  have hbR : (0 : ℝ) ≤ buffer := by exact_mod_cast hb
  have hh := (logPrimeMeshStep_pos (range_lt R) mesh).le
  have hsmall : 15 * logPrimeMeshStep (R.epsilon : ℝ) (ceiling : ℝ) mesh < m := by
    linarith
  have hbaseNorm : slopeNorm (fun i => b.cap.slope i - base.cap.slope i) ≤ 15 := by
    simpa [base, initialRow] using
      (source_slopeNorm_le b).trans (by norm_num : (15 : ℝ) / 2 ≤ 15)
  have hbase : 0 < gapLower b.cap base.cap (box R code) :=
    positive_gap_from_original_point R code x hx b.cap base.cap m hbaseNorm
      (by simpa [base, initialRow, AffineBranch.eval] using hfloor) hsmall
  have hpointRows (c : SelectedBranchData) (hc : c ∈ rows) (hne : c ≠ b) :
      m ≤ b.cap.eval x - c.cap.eval x := by
    obtain ⟨J, hJ, hJside, _, _⟩ := alternatives_source R buffer rank code c hc
    have hJne : J ≠ mask := by
      intro heq
      subst J
      have heqSome := hJside.symm.trans hscreen.1
      exact hne (Option.some_inj.mp heqSome)
    rw [lowerSide_eval_actual_v R code J c hJside x hx]
    exact hwinner J hJ hJne
  have hgapRows (c : SelectedBranchData) (hc : c ∈ rows) (hne : c ≠ b) :
      0 < gapLower b.cap c.cap (box R code) :=
    positive_gap_from_original_point R code x hx b.cap c.cap m
      (source_difference_norm_le b c) (hpointRows c hc hne) hsmall
  have hstable : stableAlternative R rank code buffer base rows b := by
    refine ⟨hscreen.2, Or.inr hbase, ?_⟩
    intro c hc
    by_cases heq : c = b
    · exact Or.inl (congrArg SelectedBranchData.cap heq.symm)
    · exact Or.inr (hgapRows c hc heq)
  have hnotbase : ¬ stableBase (box R code) base rows := by
    intro hs
    rcases hs b hmem with heq | hg
    · have he := congrArg (fun a : AffineBranch 5 => a.eval x) heq
      have hp : m ≤ b.cap.eval x - base.cap.eval x := by
        simpa [base, initialRow, AffineBranch.eval] using hfloor
      linarith
    · have hgR : (0 : ℝ) < gapLower base.cap b.cap (box R code) := by exact_mod_cast hg
      have hgP := gapLower_le_eval_gap base.cap b.cap (box R code) x hx
      have hp : m ≤ b.cap.eval x - base.cap.eval x := by
        simpa [base, initialRow, AffineBranch.eval] using hfloor
      linarith
  have hu : ∀ c ∈ rows, stableAlternative R rank code buffer base rows c → c = b := by
    intro c hc hs
    by_contra hne
    have hp := hpointRows c hc hne
    rcases hs.2.2 b hmem with heq | hg
    · have he := congrArg (fun a : AffineBranch 5 => a.eval x) heq
      linarith
    · have hgR : (0 : ℝ) < gapLower c.cap b.cap (box R code) := by exact_mod_cast hg
      have hgP := gapLower_le_eval_gap c.cap b.cap (box R code) x hx
      linarith
  have hfirst := firstStable_unique hmem hstable hu
  refine ⟨?_, hscreen.2⟩
  simpa only [select, hcanon, bank, if_neg hnotbase] using hfirst

-- This is the actual frozen output, not just an unused candidate bound.
theorem checkedCap_eq_and_error_of_original_winner (R : PairRange) (mesh : ℕ)
    (rank : Fin 6) (code : Code mesh) (hcanon : prefixCode rank.val code = code)
    (x : Fin 5 → ℝ) (hx : inBox (box R code) x)
    (mask : Finset (Fin 5)) (hm : mask ∈ tentMasks rank) (right : Bool)
    (buffer floor : ℚ) (hb : 0 ≤ buffer) (m : ℝ) (hm0 : 0 < m)
    (hmesh : 16 * logPrimeMeshStep (R.epsilon : ℝ) (ceiling : ℝ) mesh + buffer < m)
    (hside : m ≤ (otherRow R code mask right).cap.eval x -
      (chosenRow R code mask right).cap.eval x)
    (hfull : strictSquareGates ((chosenRow R code mask right).cap.eval x - m) 0
      ((pointSlots rank code mask x).map Slot.exponent))
    (hselected : strictSquareGates ((chosenRow R code mask right).cap.eval x - m)
      (selectedWord (pointSlots rank code mask x)).sum
      (remainingWord (pointSlots rank code mask x)))
    (hfloor : (floor : ℝ) + m ≤ (chosenRow R code mask right).cap.eval x)
    (hwinner : ∀ J ∈ tentMasks rank, J ≠ mask →
      m ≤ (chosenRow R code mask right).cap.eval x - VariableEnvelope.v (∑ i ∈ J, x i))
    (parent : ℝ) (hparent : parent + m ≤ (chosenRow R code mask right).cap.eval x)
    (htop : (chosenRow R code mask right).cap.eval x ≤ (153 : ℝ) / 256)
    (harrival : rank.val = 4 → x 0+x 1+x 2+3*x 3+m ≤ parent) :
    checkedCap R (bank R mesh buffer floor) buffer rank parent code =
        (rowCap R code buffer (chosenRow R code mask right) : ℝ) ∧
      0 ≤ (chosenRow R code mask right).cap.eval x -
        checkedCap R (bank R mesh buffer floor) buffer rank parent code ∧
      (chosenRow R code mask right).cap.eval x -
        checkedCap R (bank R mesh buffer floor) buffer rank parent code ≤
        (15/2 : ℝ) * logPrimeMeshStep (R.epsilon : ℝ) (ceiling : ℝ) mesh + buffer := by
  have hs := (original_strict_winner_selected R mesh rank code hcanon x hx mask hm
    right buffer floor hb m hm0 hmesh hside hfull hselected hfloor hwinner).1
  have hf := original_actual_parent_fresh R code rank x hx
    (chosenRow R code mask right) buffer hb m hmesh parent hparent htop harrival
  have hc : checkedCap R (bank R mesh buffer floor) buffer rank parent code =
      (rowCap R code buffer (chosenRow R code mask right) : ℝ) := by
    simp [checkedCap, checkedChoice, hcanon, hs, hf, CapChoice.freeze]
  refine ⟨hc, ?_⟩
  rw [hc]
  exact candidate_cap_error R code x hx (chosenRow R code mask right) buffer hb

-- The original fourth ideal cube is transferred through a previous-rank
-- one-sided error. Parent here is the already computed cap3; the rank-four
-- selector and its cap approximation are CONCLUSIONS. The source/winner
-- margins needed above may use the smaller residual margin m-error.
theorem fourth_actual_arrival_from_induction (R : PairRange) (mesh : ℕ)
    (buffer floor : ℚ) (root : ℝ) (code : Code mesh) (x : Fin 5 → ℝ)
    (C3 error m : ℝ)
    (herror : C3 - cap3 R (bank R mesh buffer floor) buffer root code ≤ error)
    (hcube : x 0+x 1+x 2+3*x 3+m ≤ C3) :
    x 0+x 1+x 2+3*x 3+(m-error) ≤
      cap3 R (bank R mesh buffer floor) buffer root code := by
  linarith

end
end ImbalancedChen.P2OriginalActiveTentSelectorApproximation
