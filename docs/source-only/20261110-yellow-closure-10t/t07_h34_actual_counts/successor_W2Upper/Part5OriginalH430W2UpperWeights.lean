import ImbalancedChen.Part5OriginalH430W2UpperStripMass
import ImbalancedChen.Part5OriginalH430W2UpperArchiveData

namespace ImbalancedChen.Part5OriginalH430W2UpperWeights

open Set MeasureTheory
open Part5OriginalH430W2UpperQuadrature Part5OriginalH430W2UpperPolygons
open Part5OriginalH430W2UpperStripMass Part5OriginalH430W2UpperArchiveData
open P5OriginalActionMassBound Part5OriginalH430LiteralBankBudget
open Part5OriginalH430ArithmeticAtomRows Part5OriginalH430BankSlotTargets
open P2Selected430LiteralActionData (rows)
open Part5OriginalH430ActualFeedbackQuotientRemainders

def expanded (j : Fin 36) : Bool := decide (3≤j.val)

def weightAt (xs : List (ℕ × ℤ)) (i : ℕ) : ℤ :=
  (xs.map (fun w => if w.1=i then w.2 else 0)).sum

def grouped (j : Fin 36) := weights j 0 ++ weights j 1 ++ weights j 2 ++ weights j 3

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The two source archives are the actual ordered upperWeights lists, with repeats retained. -/
theorem original_lists (j : Fin 36) : grouped j = (rows (slotOfAction (.inr j))).upperWeights := by
  fin_cases j <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem original_pair_census :
    (∑ j : Fin 36, if j.val<3 then (grouped j).length else 0) = 628 ∧
    (∑ j : Fin 36, if 3≤j.val then (grouped j).length else 0) = 5224 ∧
    (∑ j : Fin 36, if 3≤j.val then ∑ k : Fin 4,stripCount j k else 0) = 12624 := by
  decide

/-- All affine cuts are reconstructed even when a cell weight is zero. -/
def shapeCheck (j : Fin 36) (k : Fin 4) : Bool :=
  let p := parameterQ j
  ((weights j k).all (fun w => decide (w.1<200 ∧ 0≤w.2)) &&
    decide (((List.range 200).map (fun i => (pieces p k i).length)).sum = stripCount j k)) &&
    (List.range 200).all (fun i =>
      let xs := pieces p k i
      xs.all (fun s => decide (Fit p k i s)) && decide (Separated xs))

def numericCheck (j : Fin 36) (k : Fin 4) (i : ℕ) : Bool :=
  let w := weightAt (weights j k) i
  if w≤0 then true else
    decide ((w : ℚ)/(2^80 : ℚ) ≤
      ((pieces (parameterQ j) k i).map (stripLower (expanded j))).sum)

def laneCheck (j : Fin 36) (k : Fin 4) : Bool :=
  shapeCheck j k && (List.range 200).all (numericCheck j k)

/-- Verified interpretation of the closed, action- and Gamma-specific arithmetic computation.
The integrand, polygon and panel enclosure are fixed before the archive numeral is read. -/
theorem checked_pair_weight (j : Fin 36) (k : Fin 4) (i : Fin 200)
    (hc : laneCheck j k = true) :
    (weightAt (weights j k) i.val : ℝ)/(2^80 : ℝ) ≤ pairIntegralAtom (originalW2At j) k (.inl i) := by
  let p := parameterQ j
  have hp : W2Geometry (physical p) := by
    change W2Geometry (physical (parameterQ j))
    rw [original_parameters j]
    exact originalRepairedW2Bank_geometry _ (originalW2At_mem j)
  have hnr : 0≤pairIntegralAtom (originalW2At j) k (.inl i) :=
    MeasureTheory.integral_nonneg_of_ae (Filter.Eventually.of_forall pairKernel_nonneg)
  let w := weightAt (weights j k) i.val
  by_cases hw : w≤0
  · exact (div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hw) (by positivity)).trans hnr
  · have hboth := Bool.and_eq_true.mp hc
    have hg := (Bool.and_eq_true.mp hboth.1).2
    have hi := List.mem_range.mpr i.isLt
    have hsi := Bool.and_eq_true.mp ((List.all_eq_true.mp hg) i.val hi)
    have hf : ∀ s∈pieces p k i.val, Fit p k i.val s :=
      fun s h => of_decide_eq_true ((List.all_eq_true.mp hsi.1) s h)
    have hsep : Separated (pieces p k i.val) := of_decide_eq_true hsi.2
    have hv := (List.all_eq_true.mp hboth.2) i.val hi
    change (if w≤0 then true else decide ((w : ℚ)/(2^80 : ℚ) ≤
      ((pieces p k i.val).map (stripLower (expanded j))).sum)) = true at hv
    rw [if_neg hw] at hv
    have ha := of_decide_eq_true hv
    have hR : (w : ℝ)/(2^80 : ℝ) ≤
        ((((pieces p k i.val).map (stripLower (expanded j))).sum : ℚ) : ℝ) := by exact_mod_cast ha
    rw [← original_parameters j]
    exact hR.trans (actual_pair_atom_lower hp (expanded j) hf hsep)

end ImbalancedChen.Part5OriginalH430W2UpperWeights
