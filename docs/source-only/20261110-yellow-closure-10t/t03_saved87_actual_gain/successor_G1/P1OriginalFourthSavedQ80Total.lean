import ImbalancedChen.P1OriginalFourthRowQ80Integral
import ImbalancedChen.CurrentUpperEighteenBudget

/-! The original 3,699,127 wire rows are the only geometric inputs.
The historical Q80 sum is obtained by summing four separate lower
floors, with an array view of the very same 8193 table integers.
The closed computation has not been executed while authoring. -/
namespace ImbalancedChen.P1OriginalFourthSavedQ80Total
noncomputable section
open P1OriginalPrefixRowDecodeSoundness P1OriginalFourthPackedTable
open P1OriginalFourthPackedTable.Metadata (derivativeLowerUnits)
open P1OriginalFourthRowQ80Integral P1OriginalFourthN8193
open P5OriginalFourthFifthSourceInputs

def arrayLookup (a : Array ℕ) (j : ℕ) : ℕ := a[j]?.getD 0

theorem original_lookup : arrayLookup derivativeLowerUnits.toArray = stored := by
  funext j
  simp only [arrayLookup,stored,List.getElem?_toArray,List.getD_eq_getElem?_getD]

def addRows (lookup : ℕ → ℕ) (rows : List FourthWireRow) (s : ℤ) : ℤ :=
  rows.foldl (fun total r => total+rowUnits lookup r) s

def savedUnits : ℤ := 4*10601625247768616959055

def originalSumCheck : Bool :=
  match decodeWireRows originalFourthBytes with
  | none => false
  | some rows => decide (addRows (arrayLookup derivativeLowerUnits.toArray) rows 0 = savedUnits)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
theorem original_sum_check : originalSumCheck = true := by decide

theorem original_sum : addRows stored originalFourthWireRows 0 = savedUnits := by
  have h := original_sum_check
  simpa only [originalSumCheck,originalFourth_parse,original_lookup,decide_eq_true_eq] using h

private theorem sum_sound (rows : List FourthWireRow)
    (hm : ∀ r ∈ rows, r ∈ originalFourthWireRows) (s : ℤ) :
    (addRows stored rows s:ℝ)/2^80 ≤ (s:ℝ)/2^80+(rows.map limitingRowIntegral).sum := by
  induction rows generalizing s with
  | nil => simp [addRows]
  | cons r rs ih =>
    have h := ih (fun q hq => hm q (List.mem_cons_of_mem _ hq)) (s+rowUnits stored r)
    have ho := original_row_floor r (hm _ List.mem_cons_self)
    change (addRows stored rs (s+rowUnits stored r):ℝ)/2^80 ≤ _
    rw [Int.cast_add,add_div] at h
    simp only [List.map_cons,List.sum_cons]
    linarith only [h,ho]

/-- The precise published fourth saving is below the true sum of its
original unbuffered physical row integrals. Each original occurrence
is still present here; the geometric ownership theorem handles the union. -/
theorem original_gain_le_sum_limiting_row_integrals :
    (10601625247768616959055:ℝ)/2^78 ≤ (originalFourthWireRows.map limitingRowIntegral).sum := by
  have h := sum_sound originalFourthWireRows (fun _ hr => hr) 0
  rw [original_sum] at h
  norm_num only [savedUnits,Int.cast_mul,Int.cast_ofNat,Int.cast_zero,zero_div,zero_add] at h
  exact le_trans (le_of_eq (by norm_num)) h

theorem adopted_gain_le_sum_limiting_row_integrals :
    currentUpperEighteenGains 0 ≤ (originalFourthWireRows.map limitingRowIntegral).sum := by
  change (10601625247768616959055:ℝ)/2^78 ≤ _
  exact original_gain_le_sum_limiting_row_integrals

end
end ImbalancedChen.P1OriginalFourthSavedQ80Total
