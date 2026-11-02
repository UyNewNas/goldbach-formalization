import ImbalancedChen.P2HistoricalBankLogWeights
import ImbalancedChen.P2OriginalW1CandidateIntegerABI
import ImbalancedChen.P2HistoricSavedOrdinaryDefectAssembly

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original producer has only one kind of lower-array update: the
ordinary Buchstab suffix, followed by retention.  All70 W1 and all36 W2
write only H and all candidates read the immutable old table.  This file
proves from that literal update rule that, starting with the original
zero lower seed, every later h entry is exactly the LAST preceding H
suffix.  No earlier h analytic licence is needed.  The proof permits
changing banks/baselines between rounds, so it does not identify the
frozen184+64 history with the separate seed-only430 history.

The exact historical logarithmic algorithm is supplied by the preceding
module.  The final analytic theorem requires only previous H endpoints;
it derives, rather than assumes, all next h endpoints.  It does NOT
prove those previous H endpoints, identify stored h248 with this
recursion, or assert BankEndpointLicences.  The actual17572 saved-floor
consumer and its full ordinary-plus-defect target are unchanged.
-/

namespace ImbalancedChen.P2HistoricalLowerBankAncestry

noncomputable section

open P2TableActionSourceOnly P2SimultaneousTableSourceOnly
open P2HistoricalBankLogWeights
open P2HistoricSavedOrdinaryDefectAssembly (bankCellRight)
open Wu2008DoubleSieve
open scoped BigOperators

abbrev W1Action := P2OriginalW1CandidateIntegerABI.Action
abbrev W2Action := P2OriginalW2CandidateIntegerABI.Action

/-- Original2327/100000 seed, rounded down once, with exactly sixty H
cells and a zero lower array.  This definition is not its analytic licence. -/
def originalSeed : Table := fun upper i =>
  if upper then if i.val < 60 then (2327 * (tableQ : ℤ)) / 100000 else 0 else 0

theorem originalSeed_nonnegative : Nonnegative originalSeed := by
  intro upper i
  cases upper
  · exact le_rfl
  · simp only [originalSeed, if_true]
    split_ifs
    · exact Int.ediv_nonneg (mul_nonneg (by norm_num) (by positivity)) (by norm_num)
    · exact le_rfl

/-- Both source Buchstab writes read old; the guard is on the LEFT
endpoint, hence i=49 (right endpoint2) remains zero. -/
def buchstabStep (old : Table) : Table := fun upper i =>
  if 50 ≤ i.val then
    max (old upper i)
      (suffixNumerator historicalLogWeights old (!upper)
        (if upper then max 50 (i.val-49) else i.val-49))
  else old upper i

def applyW1Bank (old : Table) (current : Table) : List W1Action → Table
  | [] => current
  | a :: bank => applyW1Bank old (P2OriginalW1CandidateIntegerABI.apply old current a) bank

def applyW2Bank (old : Table) (current : Table) : List W2Action → Table
  | [] => current
  | a :: bank => applyW2Bank old (P2OriginalW2CandidateIntegerABI.apply old current a) bank

/-- One exact original round; no candidate reads the accumulating table. -/
def oneRound (old : Table) (w1 : List W1Action) (w2 : List W2Action) : Table :=
  applyW2Bank old (applyW1Bank old (buchstabStep old) w1) w2

theorem applyW1Bank_lower (old current : Table) (bank : List W1Action) (i : Fin 200) :
    applyW1Bank old current bank false i = current false i := by
  induction bank generalizing current with
  | nil => rfl
  | cons a bank ih =>
      rw [applyW1Bank, ih, P2OriginalW1CandidateIntegerABI.apply_lower_unchanged]

theorem applyW2Bank_lower (old current : Table) (bank : List W2Action) (i : Fin 200) :
    applyW2Bank old current bank false i = current false i := by
  induction bank generalizing current with
  | nil => rfl
  | cons a bank ih =>
      rw [applyW2Bank, ih, P2OriginalW2CandidateIntegerABI.apply_lower_unchanged]

theorem applyW1Bank_retains (old current : Table) (bank : List W1Action) :
    Below current (applyW1Bank old current bank) := by
  induction bank generalizing current with
  | nil => exact fun _ _ => le_rfl
  | cons a bank ih =>
      intro upper i
      exact (P2OriginalW1CandidateIntegerABI.apply_retains old current a upper i).trans
        (ih (P2OriginalW1CandidateIntegerABI.apply old current a) upper i)

theorem applyW2Bank_retains (old current : Table) (bank : List W2Action) :
    Below current (applyW2Bank old current bank) := by
  induction bank generalizing current with
  | nil => exact fun _ _ => le_rfl
  | cons a bank ih =>
      intro upper i
      exact (P2OriginalW2CandidateIntegerABI.apply_retains old current a upper i).trans
        (ih (P2OriginalW2CandidateIntegerABI.apply old current a) upper i)

theorem oneRound_retains (old : Table) (w1 : List W1Action) (w2 : List W2Action) :
    Below old (oneRound old w1 w2) := by
  intro upper i
  have hb : old upper i ≤ buchstabStep old upper i := by
    unfold buchstabStep
    split_ifs
    · exact le_max_left _ _
    · exact le_rfl
  exact hb.trans ((applyW1Bank_retains old (buchstabStep old) w1 upper i).trans
    (applyW2Bank_retains old (applyW1Bank old (buchstabStep old) w1) w2 upper i))

theorem oneRound_lower (old : Table) (w1 : List W1Action) (w2 : List W2Action)
    (i : Fin 200) :
    oneRound old w1 w2 false i =
      if 50 ≤ i.val then
        max (old false i) (suffixNumerator historicalLogWeights old true (i.val-49))
      else old false i := by
  rw [oneRound, applyW2Bank_lower, applyW1Bank_lower]
  simp only [buchstabStep, Bool.not_false, Bool.false_eq_true, if_false]

/-- The banks can change at the original generation boundaries. -/
def iterate (w1 : ℕ → List W1Action) (w2 : ℕ → List W2Action) : ℕ → Table
  | 0 => originalSeed
  | n+1 => oneRound (iterate w1 w2 n) (w1 n) (w2 n)

theorem iterate_retains (w1 : ℕ → List W1Action) (w2 : ℕ → List W2Action) (n : ℕ) :
    Below (iterate w1 w2 n) (iterate w1 w2 (n+1)) :=
  oneRound_retains _ _ _

theorem iterate_nonnegative (w1 : ℕ → List W1Action) (w2 : ℕ → List W2Action)
    (n : ℕ) : Nonnegative (iterate w1 w2 n) := by
  induction n with
  | zero => exact originalSeed_nonnegative
  | succ n ih =>
      intro upper i
      exact (ih upper i).trans (iterate_retains w1 w2 n upper i)

theorem suffix_nonnegative {old : Table} (hn : Nonnegative old)
    (upper : Bool) (k : ℕ) :
    0 ≤ suffixNumerator historicalLogWeights old upper k := by
  apply Finset.sum_nonneg
  intro j _
  exact Int.ediv_nonneg
    (mul_nonneg (read_nonnegative hn upper (k+j)) (logWeight_nonnegative (k+j)))
    (by exact_mod_cast tableQ_pos.le)

/-- A genuine ancestry elimination: all retained earlier lower outputs
are dominated by the latest suffix, since H is retained and the literal
weights are nonnegative.  There is no count/endpoint hypothesis. -/
theorem iterate_lower_last_suffix (w1 : ℕ → List W1Action) (w2 : ℕ → List W2Action)
    (n : ℕ) (i : Fin 200) :
    iterate w1 w2 (n+1) false i =
      if 50 ≤ i.val then
        suffixNumerator historicalLogWeights (iterate w1 w2 n) true (i.val-49)
      else 0 := by
  induction n with
  | zero =>
      rw [iterate, oneRound_lower]
      by_cases hi : 50 ≤ i.val
      · simp only [if_pos hi]
        exact max_eq_right (suffix_nonnegative originalSeed_nonnegative true _)
      · simp only [if_neg hi, iterate, originalSeed, Bool.false_eq_true, if_false]
  | succ n ih =>
      rw [iterate, oneRound_lower]
      by_cases hi : 50 ≤ i.val
      · simp only [if_pos hi]
        rw [ih, if_pos hi]
        exact max_eq_right (suffixNumerator_mono historicalLogWeights
          (iterate_retains w1 w2 n) true (by omega))
      · simp only [if_neg hi]
        rw [ih, if_neg hi]

/-- The only analytic predecessor needed by the lower-array branch. -/
def UpperEndpoints (δ : ℝ) (old : Table) : Prop :=
  ∀ i : Fin 200, (old true i : ℝ)/tableQ ≤ H δ (tableGrid (i.val+1))

theorem historical_lower_suffix_sound {δ : ℝ} {old : Table}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) (hn : Nonnegative old)
    (hupper : UpperEndpoints δ old) (i : Fin 200) (hi : 50 ≤ i.val) :
    (suffixNumerator historicalLogWeights old true (i.val-49) : ℝ)/tableQ ≤
      h δ (tableGrid (i.val+1)) := by
  have hold (j : ℕ) (hj : j < 200) :
      (read old true j : ℝ)/tableQ ≤ wuImprovementLimit true δ (tableGrid (j+1)) := by
    simpa only [read, dif_pos hj, H] using hupper ⟨j,hj⟩
  have ht := rounded_original_grid_tail_sound true (read old true) logWeight
    hδ hδhi tableQ_pos (show i.val-49 ≤ 200 by omega)
    (show (if true then 0 else 50 : ℕ) ≤ i.val-49 by omega)
    (fun j _ => read_nonnegative hn true j)
    (fun j _ => logWeight_nonnegative j) hold (fun j _ => logWeight_le_log j)
  rw [← suffixNumerator_scaled historicalLogWeights old true (i.val-49),
    tableGrid_lower_start hi] at ht
  have hs2 : 2 ≤ tableGrid (i.val+1) := by
    have hg := tableGrid_mono (show 50 ≤ i.val+1 by omega)
    simpa [tableGrid] using hg
  have hs5 := (tableGrid_bounds (show i.val+1 ≤ 200 by omega)).2
  exact ht.trans (buchstab_lower_integral_sound hδ hδhi hs2 hs5)

/-- All next lower endpoints follow from the preceding H array only.
Below the producer's left-endpoint guard the actual lower array is zero,
including the boundary cell with right endpoint2. -/
theorem iterate_lower_endpoints {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10)
    (w1 : ℕ → List W1Action) (w2 : ℕ → List W2Action) (n : ℕ)
    (hupper : UpperEndpoints δ (iterate w1 w2 n)) (i : Fin 200) :
    (iterate w1 w2 (n+1) false i : ℝ)/tableQ ≤ h δ (tableGrid (i.val+1)) := by
  rw [iterate_lower_last_suffix]
  by_cases hi : 50 ≤ i.val
  · rw [if_pos hi]
    exact historical_lower_suffix_sound hδ hδhi (iterate_nonnegative w1 w2 n) hupper i hi
  · rw [if_neg hi, Int.cast_zero, zero_div]
    have hb := tableGrid_bounds (show i.val+1 ≤ 200 by omega)
    exact wuImprovementLimit_nonneg false hδ (by linarith : δ < 1/2)
      hb.1 (hb.2.trans (by norm_num))

theorem bankCellRight_fin (i : Fin 200) :
    (bankCellRight (i.val : ℤ) : ℝ) = tableGrid (i.val+1) := by
  simp [bankCellRight, tableGrid]

/-- Exact H247 -> h248 analytic dependency, at the original bank's
endpoints.  It intentionally does not identify this algorithmic lower
array with bankLowerTable, nor supply the still missing H247 licence. -/
theorem historical_248_lower_from_H247 {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10)
    (w1 : ℕ → List W1Action) (w2 : ℕ → List W2Action)
    (hupper : UpperEndpoints δ (iterate w1 w2 247)) (i : Fin 200) :
    (iterate w1 w2 248 false i : ℝ)/tableQ ≤ h δ (bankCellRight (i.val : ℤ) : ℝ) := by
  rw [bankCellRight_fin]
  exact iterate_lower_endpoints hδ hδhi w1 w2 247 hupper i

end
end ImbalancedChen.P2HistoricalLowerBankAncestry
