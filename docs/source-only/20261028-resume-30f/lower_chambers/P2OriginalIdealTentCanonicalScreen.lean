import ImbalancedChen.P2OriginalCanonicalPairTentBank
import ImbalancedChen.P2OriginalTentSquarePerturbation
import ImbalancedChen.P2OriginalUniformMixedTentWChoice

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Original ideal tent margins imply the concrete canonical tent bank's
screened membership. The canonical bank, literal SourceForm/mask, physical
point/upper slot words and both full/selected-complement gates are retained.
There is no sourceCheck, lowerSide result or bank-membership premise.
The bank is explicitly the independent tent subbank, not a full W policy.
-/

namespace ImbalancedChen.P2OriginalIdealTentCanonicalScreen

noncomputable section
open scoped Classical BigOperators
open Set
open P2PhysicalIncomingPrefixCells P2EnhancedLowerPhysicalNode
open P2OriginalLowerSelectedCapConstructor (Code strictSquareGates)
open P2OriginalLowerAffineTieSelector
open P2OriginalLowerBufferedAffineBoxes
open P2OriginalLowerWholeBoxBranchSelect
open P2OriginalLowerFiniteAffineMeshWidth (slopeNorm affine_oscillation)
open P2OriginalUniformMixedTentWChoice (source_slopeNorm_le source_difference_norm_le)
open P2OriginalPairSourceReceiver
open P2OriginalCanonicalPairTentBank
open P2OriginalTentSquarePerturbation

def chosenRow (R : PairRange) {mesh : ℕ} (code : Code mesh)
    (mask : Finset (Fin 5)) (right : Bool) : SelectedBranchData :=
  if right then rightRow R code mask else leftRow R code mask

def otherRow (R : PairRange) {mesh : ℕ} (code : Code mesh)
    (mask : Finset (Fin 5)) (right : Bool) : SelectedBranchData :=
  chosenRow R code mask (!right)

@[simp] theorem chosenRow_mask (R : PairRange) {mesh : ℕ} (code : Code mesh)
    (mask : Finset (Fin 5)) (right : Bool) :
    (chosenRow R code mask right).form.supportMask = mask := by
  cases right <;> rfl

private theorem range_lt (R : PairRange) : (R.epsilon : ℝ) < (ceiling : ℝ) := by
  exact_mod_cast (lt_trans R.epsilon_lt_a (by norm_num [ceiling] : (417 : ℚ)/5000 < ceiling))

private theorem qPoint_cast (R : PairRange) (mesh j : ℕ) :
    (qPoint R mesh j : ℝ) = logPrimeMeshPoint (R.epsilon : ℝ) (ceiling : ℝ) mesh j := by
  unfold qPoint logPrimeMeshPoint logPrimeMeshStep
  push_cast
  ring

private theorem box_width (R : PairRange) {mesh : ℕ} (code : Code mesh) (i : Fin 5) :
    ((box R code).hi i : ℝ) - (box R code).lo i ≤
      logPrimeMeshStep (R.epsilon : ℝ) (ceiling : ℝ) mesh := by
  cases hc : (code i).1 with
  | none => simpa [box, qLo, qHi, hc] using (logPrimeMeshStep_pos (range_lt R) mesh).le
  | some j =>
      simp only [box, hc, qLo, qHi, qPoint_cast, logPrimeMeshPoint_succ]
      linarith

private theorem vertex_in_box (R : PairRange) {mesh : ℕ} (code : Code mesh)
    (x : Fin 5 → ℝ) (hx : inBox (box R code) x) (slope : Fin 5 → ℚ) :
    inBox (box R code) (fun i => (lowerVertex slope (box R code) i : ℝ)) := by
  intro i
  have hlohi := (hx i).1.trans (hx i).2
  by_cases hs : 0 ≤ slope i
  · simpa [lowerVertex, hs] using And.intro (le_refl ((box R code).lo i : ℝ)) hlohi
  · simpa [lowerVertex, hs] using And.intro hlohi (le_refl ((box R code).hi i : ℝ))

-- This is for the independent PairRange box, not the smaller ordinary a/h
-- grid. It supplies the real whole-box loss used by the concrete producer.
theorem ideal_minus_boxInf_le_step (R : PairRange) {mesh : ℕ}
    (code : Code mesh) (x : Fin 5 → ℝ) (hx : inBox (box R code) x)
    (constant : ℚ) (slope : Fin 5 → ℚ) :
    affineValue constant slope x -
      (wholeBoxInfimum constant slope (box R code) : ℝ) ≤
      slopeNorm slope * logPrimeMeshStep (R.epsilon : ℝ) (ceiling : ℝ) mesh := by
  let y : Fin 5 → ℝ := fun i => lowerVertex slope (box R code) i
  have hy : inBox (box R code) y := vertex_in_box R code x hx slope
  have hcoord (i : Fin 5) : |x i - y i| ≤
      logPrimeMeshStep (R.epsilon : ℝ) (ceiling : ℝ) mesh := by
    have hle : |x i - y i| ≤ ((box R code).hi i : ℝ) - (box R code).lo i := by
      exact abs_le.mpr ⟨by linarith [(hx i).1, (hx i).2, (hy i).1, (hy i).2],
        by linarith [(hx i).1, (hx i).2, (hy i).1, (hy i).2]⟩
    exact hle.trans (box_width R code i)
  have hosc := affine_oscillation constant slope x y _ hcoord
  have heq : affineValue constant slope y =
      (wholeBoxInfimum constant slope (box R code) : ℝ) := by
    simp [affineValue, wholeBoxInfimum, y]
  rw [heq] at hosc
  exact (le_abs_self _).trans hosc

private theorem side_gap_pos (R : PairRange) {mesh : ℕ}
    (code : Code mesh) (x : Fin 5 → ℝ) (hx : inBox (box R code) x)
    (b c : SelectedBranchData) (margin : ℝ)
    (hpoint : margin ≤ c.cap.eval x - b.cap.eval x)
    (hwidth : 15 * logPrimeMeshStep (R.epsilon : ℝ) (ceiling : ℝ) mesh < margin) :
    0 < gapLower c.cap b.cap (box R code) := by
  have hstep0 := (logPrimeMeshStep_pos (range_lt R) mesh).le
  have hnorm := mul_le_mul_of_nonneg_right (source_difference_norm_le c b) hstep0
  have hloss := ideal_minus_boxInf_le_step R code x hx
    (c.cap.constant - b.cap.constant) (fun i => c.cap.slope i - b.cap.slope i)
  have heval : affineValue (c.cap.constant - b.cap.constant)
      (fun i => c.cap.slope i - b.cap.slope i) x = c.cap.eval x - b.cap.eval x := by
    simp [affineValue, AffineBranch.eval, Rat.cast_sub, sub_mul, Finset.sum_sub_distrib]
    ring
  rw [heval] at hloss
  have hpos : (0 : ℝ) < gapLower c.cap b.cap (box R code) := by
    change (0 : ℝ) < (wholeBoxInfimum (c.cap.constant - b.cap.constant)
      (fun i => c.cap.slope i - b.cap.slope i) (box R code) : ℝ)
    linarith
  exact_mod_cast hpos

-- Point full/complement gates are required at ideal cap minus the actual
-- positive chamber margin, not at a boxed candidate or an ideal parent.
-- The 16-step budget covers 15-step side separation and 15/2+6 square loss.
theorem ideal_tent_enters_concrete_screen (R : PairRange) {mesh : ℕ}
    (code : Code mesh) (rank : Fin 6) (x : Fin 5 → ℝ)
    (hx : inBox (box R code) x) (mask : Finset (Fin 5))
    (hmask : mask ∈ P2OriginalFiniteTentBankSelectorMargins.tentMasks rank)
    (right : Bool) (buffer : ℚ) (hbuffer : 0 ≤ buffer)
    (margin : ℝ) (hmargin : 0 < margin)
    (hbudget : 16 * logPrimeMeshStep (R.epsilon : ℝ) (ceiling : ℝ) mesh + buffer < margin)
    (hside : margin ≤ (otherRow R code mask right).cap.eval x -
      (chosenRow R code mask right).cap.eval x)
    (hfull : strictSquareGates ((chosenRow R code mask right).cap.eval x - margin) 0
      ((pointSlots rank code mask x).map Slot.exponent))
    (hselected : strictSquareGates ((chosenRow R code mask right).cap.eval x - margin)
      (selectedWord (pointSlots rank code mask x)).sum
      (remainingWord (pointSlots rank code mask x))) :
    lowerSide R code mask = some (chosenRow R code mask right) ∧
      sourceCheck R rank code buffer (chosenRow R code mask right) := by
  let b := chosenRow R code mask right
  let c := otherRow R code mask right
  let h := logPrimeMeshStep (R.epsilon : ℝ) (ceiling : ℝ) mesh
  have hh : 0 ≤ h := (logPrimeMeshStep_pos (range_lt R) mesh).le
  have hb : (0 : ℝ) ≤ buffer := by exact_mod_cast hbuffer
  have hgap := side_gap_pos R code x hx b c margin hside (by dsimp [h] at *; linarith)
  have hsideCheck : sideCheck b (box R code) := by
    cases right <;> simpa [b, c, chosenRow, otherRow, sideCheck, SourceForm.otherTent] using hgap.le
  have hLower : lowerSide R code mask = some b := by
    cases right with
    | false => simp [lowerSide, b, c, chosenRow, otherRow, hgap.le]
    | true =>
        have hn : ¬ 0 ≤ gapLower (rightRow R code mask).cap (leftRow R code mask).cap (box R code) := by
          intro hg
          have hbound := gapLower_le_eval_gap (rightRow R code mask).cap
            (leftRow R code mask).cap (box R code) x hx
          have hgR : (0 : ℝ) ≤ gapLower (rightRow R code mask).cap (leftRow R code mask).cap (box R code) := by exact_mod_cast hg
          have hp : margin ≤ (leftRow R code mask).cap.eval x - (rightRow R code mask).cap.eval x := by
            simpa [b, c, chosenRow, otherRow] using hside
          linarith
        simp [lowerSide, b, c, chosenRow, otherRow, hn, hgap.le]
  have hcaploss := ideal_minus_boxInf_le_step R code x hx b.cap.constant b.cap.slope
  have hnorm := mul_le_mul_of_nonneg_right (source_slopeNorm_le b) hh
  have hcap : b.cap.eval x - margin + 6 * h ≤ (rowCap R code buffer b : ℝ) := by
    unfold rowCap
    push_cast
    have heval : affineValue b.cap.constant b.cap.slope x = b.cap.eval x := rfl
    rw [heval] at hcaploss
    dsimp [h] at *
    linarith
  have hu (i : Fin 5) : (qHi R mesh (code i).1 : ℝ) ≤ x i + h := by
    have hw := box_width R code i
    have hl := (hx i).1
    change (qLo R mesh (code i).1 : ℝ) ≤ x i at hl
    dsimp [box] at hw
    dsimp [h]
    linarith
  have hslots : List.Forall₂ (slotStep h) (pointSlots rank code mask x) (ownSlots R rank code mask) := by
    fin_cases rank <;> simp [pointSlots, ownSlots, slotStep, pointSlot, ownSlot, hu]
  have hlen : (pointSlots rank code mask x).length ≤ 5 := by
    simp only [pointSlots, List.length_take, List.length_cons, List.length_nil]
    exact min_le_right _ _
  have hsquares := full_and_selected_squares_step h _ _ hh _ _ hslots hlen hcap hfull hselected
  have helig := (original_mask_alphabet rank mask).mp hmask
  have hbform : formRankEligible rank b.form := by
    cases right <;> fin_cases rank <;> simpa [b, chosenRow, leftRow, rightRow, formRankEligible] using helig
  have hmaskPrefix : ∀ i ∈ mask, i.val < rank.val := by
    fin_cases rank <;> simp only [formRankEligible] at helig
    all_goals first
      | exact False.elim helig
      | exact helig.2
      | exact fun i _ => i.isLt
  refine ⟨hLower, hbform, hsideCheck, ?_, ?_, ?_⟩
  · simpa [b, chosenRow_mask] using hsquares.1
  · simpa [b, chosenRow_mask] using hsquares.2
  · simpa [b, chosenRow_mask] using hmaskPrefix

-- Membership is in the independently built literal canonical bank. seed
-- merely names that bank's initial inherited floor; it is not a bank input.
theorem ideal_tent_occurs_in_canonical_bank (R : PairRange) (mesh : ℕ)
    (code : Code mesh) (rank : Fin 6) (x : Fin 5 → ℝ)
    (hx : inBox (box R code) x) (mask : Finset (Fin 5))
    (hmask : mask ∈ P2OriginalFiniteTentBankSelectorMargins.tentMasks rank)
    (right : Bool) (buffer seed : ℚ) (hbuffer : 0 ≤ buffer)
    (margin : ℝ) (hmargin : 0 < margin)
    (hbudget : 16 * logPrimeMeshStep (R.epsilon : ℝ) (ceiling : ℝ) mesh + buffer < margin)
    (hside : margin ≤ (otherRow R code mask right).cap.eval x -
      (chosenRow R code mask right).cap.eval x)
    (hfull : strictSquareGates ((chosenRow R code mask right).cap.eval x - margin) 0
      ((pointSlots rank code mask x).map Slot.exponent))
    (hselected : strictSquareGates ((chosenRow R code mask right).cap.eval x - margin)
      (selectedWord (pointSlots rank code mask x)).sum (remainingWord (pointSlots rank code mask x))) :
    chosenRow R code mask right ∈ (bank R mesh buffer seed).alternatives rank code := by
  obtain ⟨hside, hcheck⟩ := ideal_tent_enters_concrete_screen R code rank x hx mask hmask
    right buffer hbuffer margin hmargin hbudget hside hfull hselected
  exact every_screened_original_action_occurs R mesh buffer seed rank code mask hmask _ hside hcheck

end
end ImbalancedChen.P2OriginalIdealTentCanonicalScreen
