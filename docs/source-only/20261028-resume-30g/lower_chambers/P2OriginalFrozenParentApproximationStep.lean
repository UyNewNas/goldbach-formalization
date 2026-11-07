import ImbalancedChen.P2OriginalRetainedTentCompactMargin

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Original ideal-parent margins are transferred through an already proved
one-sided error for the TRUE computed parent. This is an induction STEP,
not an assumed final cap convergence theorem. The positive-measure ideal
inheritance lane is also proved directly from the actual computed choice:
it preserves the preceding error, even if that choice raises its smaller
finite parent. Fifth history reads the frozen fourth state and adds no
new odd cube. Active winner coverage and the full W bank remain separate.
-/

namespace ImbalancedChen.P2OriginalFrozenParentApproximationStep

noncomputable section
open scoped Classical BigOperators
open P2LowerCapPlanIntegerRetention
open P2OriginalLowerSelectedCapConstructor (Code prefixCode)
open P2OriginalLowerWholeBoxBranchSelect
open P2OriginalLowerAffineTieSelector
open P2OriginalLowerBufferedAffineBoxes
open P2OriginalLowerFiniteAffineMeshWidth (slopeNorm)
open P2OriginalUniformMixedTentWChoice (source_slopeNorm_le)
open P2OriginalPairSourceReceiver
open P2OriginalCanonicalPairTentBank
open P2OriginalIdealTentCanonicalScreen
open P2OriginalCanonicalTentFrozenChambers

theorem candidate_cap_error (R : PairRange) {mesh : ℕ}
    (code : Code mesh) (x : Fin 5 → ℝ) (hx : inBox (box R code) x)
    (b : SelectedBranchData) (buffer : ℚ) (hb : 0 ≤ buffer) :
    0 ≤ b.cap.eval x - (rowCap R code buffer b : ℝ) ∧
      b.cap.eval x - (rowCap R code buffer b : ℝ) ≤
        (15/2 : ℝ) * logPrimeMeshStep (R.epsilon : ℝ) (ceiling : ℝ) mesh + buffer := by
  have hrange : (R.epsilon : ℝ) < (ceiling : ℝ) := by
    exact_mod_cast lt_trans R.epsilon_lt_a (by norm_num [ceiling] : (417:ℚ)/5000 < ceiling)
  have hh := (logPrimeMeshStep_pos hrange mesh).le
  have hloss := ideal_minus_boxInf_le_step R code x hx b.cap.constant b.cap.slope
  have hnorm := mul_le_mul_of_nonneg_right (source_slopeNorm_le b) hh
  have hlo := wholeBoxInfimum_le_affine b.cap.constant b.cap.slope (box R code) x hx
  have hbR : (0 : ℝ) ≤ buffer := by exact_mod_cast hb
  have heval : affineValue b.cap.constant b.cap.slope x = b.cap.eval x := rfl
  rw [heval] at hloss hlo
  have hrow : (rowCap R code buffer b : ℝ) =
      (wholeBoxInfimum b.cap.constant b.cap.slope (box R code) : ℝ) - buffer := by
    unfold rowCap
    push_cast <;> rfl
  rw [hrow]
  exact ⟨by linarith, by linarith⟩

-- The 3rd approximation is the exact cap3 of this finite policy, with
-- real root kept separate from the rational source-ranking floor.
-- Consuming its preceding error removes the old premise that a fourth
-- point was ALREADY admitted by the finite, smaller parent.
theorem fourth_fresh_from_previous_parent_error
    (R : PairRange) (mesh : ℕ) (buffer floor : ℚ) (root : ℝ)
    (hb : 0 ≤ buffer) (code : Code mesh) (x : Fin 5 → ℝ)
    (hx : inBox (box R code) x) (b : SelectedBranchData)
    (C3 error margin : ℝ) (he0 : 0 ≤ error)
    (hparent : cap3 R (bank R mesh buffer floor) buffer root code ≤ C3)
    (herror : C3 - cap3 R (bank R mesh buffer floor) buffer root code ≤ error)
    (hideal_new : C3 + margin ≤ b.cap.eval x)
    (hideal_cube : x 0+x 1+x 2+3*x 3+margin ≤ C3)
    (htop : b.cap.eval x ≤ (153:ℝ)/256)
    (hbudget : error + 16 * logPrimeMeshStep (R.epsilon : ℝ) (ceiling : ℝ) mesh + buffer < margin) :
    freshCheck R 4 code buffer (cap3 R (bank R mesh buffer floor) buffer root code) b ∧
      (0 ≤ b.cap.eval x - (rowCap R code buffer b : ℝ) ∧
        b.cap.eval x - (rowCap R code buffer b : ℝ) ≤
          (15/2 : ℝ) * logPrimeMeshStep (R.epsilon : ℝ) (ceiling : ℝ) mesh + buffer) := by
  refine ⟨?_, candidate_cap_error R code x hx b buffer hb⟩
  apply rank4_actual_frozen_parent_chamber R mesh buffer floor root hb code x hx b
    (margin-error) (by linarith) (by linarith) htop
  linarith

-- No fourth improvement is assumed. The preceding cap4 may be inherited;
-- only its one-sided comparison with the ideal parent enters this step.
theorem fifth_fresh_from_previous_parent_comparison
    (R : PairRange) (mesh : ℕ) (buffer floor : ℚ) (root : ℝ)
    (hb : 0 ≤ buffer) (code : Code mesh) (x : Fin 5 → ℝ)
    (hx : inBox (box R code) x) (b : SelectedBranchData) (C4 margin : ℝ)
    (hparent : cap4 R (bank R mesh buffer floor) buffer root code ≤ C4)
    (hideal_new : C4 + margin ≤ b.cap.eval x)
    (htop : b.cap.eval x ≤ (153:ℝ)/256)
    (hbudget : 16 * logPrimeMeshStep (R.epsilon : ℝ) (ceiling : ℝ) mesh + buffer < margin) :
    freshCheck R 5 code buffer (cap4 R (bank R mesh buffer floor) buffer root code) b ∧
      (0 ≤ b.cap.eval x - (rowCap R code buffer b : ℝ) ∧
        b.cap.eval x - (rowCap R code buffer b : ℝ) ≤
          (15/2 : ℝ) * logPrimeMeshStep (R.epsilon : ℝ) (ceiling : ℝ) mesh + buffer) := by
  exact ⟨rank5_actual_frozen_parent_chamber R mesh buffer floor root hb code x hx b margin
    hbudget (by linarith) htop, candidate_cap_error R code x hx b buffer hb⟩

-- Structural ideal inheritance is NOT a wall. Every tent endpoint at the
-- original point lies below C; the actual computation consequently stays
-- below C and cannot worsen the preceding parent's approximation error.
-- No choice, selector success, freshCheck or sourceCheck is an input.
theorem original_tent_inherited_step_error
    (R : PairRange) (mesh : ℕ) (buffer floor : ℚ) (hb : 0 ≤ buffer)
    (rank : Fin 6) (code : Code mesh) (hcanon : prefixCode rank.val code = code)
    (x : Fin 5 → ℝ) (hx : inBox (box R code) x) (parent C error : ℝ)
    (hparent : parent ≤ C) (herror : C-parent ≤ error)
    (hideal : ∀ mask ∈ P2OriginalFiniteTentBankSelectorMargins.tentMasks rank,
      VariableEnvelope.v (∑ i ∈ mask, x i) ≤ C) :
    0 ≤ C - checkedCap R (bank R mesh buffer floor) buffer rank parent code ∧
      C - checkedCap R (bank R mesh buffer floor) buffer rank parent code ≤ error := by
  let B := bank R mesh buffer floor
  have hmono : parent ≤ checkedCap R B buffer rank parent code :=
    checked_cap_mono R mesh buffer floor rank code parent
  have hupper : checkedCap R B buffer rank parent code ≤ C := by
    unfold checkedCap checkedChoice
    rw [hcanon]
    cases hs : select R B buffer rank code with
    | none => simpa [hs, CapChoice.freeze] using hparent
    | some b =>
        by_cases hf : freshCheck R rank code buffer parent b
        · obtain ⟨mask, hm, hside, _, _⟩ := selected_source R mesh buffer floor rank code b hs
          rw [hcanon] at hside
          have hv := lowerSide_eval_actual_v R code mask b hside x hx
          have herr := candidate_cap_error R code x hx b buffer hb
          have hcap : (rowCap R code buffer b : ℝ) ≤ C := by
            rw [hv] at herr
            linarith [hideal mask hm]
          simpa [hs, hf, CapChoice.freeze] using hcap
        · simpa [hs, hf, CapChoice.freeze] using hparent
  exact ⟨by linarith, by linarith⟩

-- The exact old even cube supplies the fifth historical square under
-- either an inherited or improved fourth cap. No S4+3*t5 condition exists.
theorem fifth_square_from_actual_fourth_history (R : PairRange) {mesh : ℕ}
    (code : Code mesh) (parent3 parent4 : ℝ)
    (harrival : arrivalGate R 4 code parent3) (hmono : parent3 ≤ parent4)
    (horder : (qHi R mesh (code 4).1 : ℝ) ≤ qHi R mesh (code 3).1) :
    (qHi R mesh (code 0).1 : ℝ) + qHi R mesh (code 1).1 + qHi R mesh (code 2).1 +
      qHi R mesh (code 3).1 + 2 * qHi R mesh (code 4).1 < parent4 := by
  have hc : (qHi R mesh (code 0).1 : ℝ) + qHi R mesh (code 1).1 +
      qHi R mesh (code 2).1 + 3 * qHi R mesh (code 3).1 < parent3 := by
    simpa [arrivalGate] using harrival
  linarith

end
end ImbalancedChen.P2OriginalFrozenParentApproximationStep
