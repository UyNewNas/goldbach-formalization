import ImbalancedChen.P1OriginalFourthDerivativeNumerator
import ImbalancedChen.P1OriginalFourthQ80LogBounds
import ImbalancedChen.P1OriginalFourthRawTableMetadata

/-! All 8193 integers stored in the original stronger fourth-prefix
derivative table against the actual ordinary normalized upper derivative.
The finite test consumes the already stored list and a running sum. -/
namespace ImbalancedChen.P1OriginalFourthN8193
open OriginalU2CoupledRecurrenceSourceOnly (upper H H_eq_one)
open Certificates.P2HistoricJTableInterpreter (q)
open P1OriginalFourthDerivativeNumerator
open P1OriginalFourthQ80LogBounds
open P1OriginalFourthPackedTable.Metadata (derivativeLowerUnits)

def node (j : ℕ) : ℝ := 3+(j:ℝ)/4096
def stored (j : ℕ) : ℕ := derivativeLowerUnits.getD j 0

def checkRows : List ℕ → ℕ → ℤ → Bool
  | [], _, _ => true
  | value::rest, j, credit =>
      decide ((value:ℤ) + penalty j = credit) && checkRows rest (j+1) (credit + leftStep j)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem original_integer_links : checkRows derivativeLowerUnits 0 (scale:ℤ) = true := by decide

set_option maxRecDepth 1000000 in
theorem original_length : derivativeLowerUnits.length = 8193 := by decide

theorem node_bounds (j : ℕ) (hj : j ≤ 8192) : 3 ≤ node j ∧ node j ≤ 5 := by
  have hh : (j:ℝ) ≤ 8192 := by exact_mod_cast hj
  dsimp only [node]
  constructor <;> linarith [Nat.cast_nonneg (α := ℝ) j]

theorem node_increment (j : ℕ) : node (j+1)-node j = 1/4096 := by
  simp [node]
  <;> ring

private theorem node_q (j : ℕ) :
    q (node j-1) = Real.log (1+(j:ℝ)/4096)/(2+(j:ℝ)/4096) := by
  unfold q node
  rw [show 3+(j:ℝ)/4096-1 = 2+(j:ℝ)/4096 by ring,
    show 2+(j:ℝ)/4096-1 = 1+(j:ℝ)/4096 by ring]

theorem leftStep_sound (j : ℕ) (hj : j < 8192) :
    (leftStep j:ℝ)/(scale:ℝ) ≤ H (node (j+1)) - H (node j) := by
  have hn := node_bounds j hj.le
  have hn' := node_bounds (j+1) (by omega)
  have hstep := node_increment j
  have hD : (0:ℝ) < 8192+j := by positivity
  have hD' : (0:ℝ) < 2+(j:ℝ)/4096 := by positivity
  have hc := (H_interval_bounds hn.1 (show node j ≤ node (j+1) by linarith) hn'.2).1
  refine le_trans ?_ hc
  rw [hstep,node_q]
  calc
    _ ≤ ((lo j:ℝ)/(8192+(j:ℝ)))/(scale:ℝ) :=
      div_le_div_of_nonneg_right (step_le j) scale_pos.le
    _ ≤ (((scale:ℝ)*Real.log (1+(j:ℝ)/4096))/(8192+(j:ℝ)))/(scale:ℝ) :=
      div_le_div_of_nonneg_right (div_le_div_of_nonneg_right (log_interval j).1 hD.le) scale_pos.le
    _ = _ := by field_simp [hD.ne',hD'.ne',scale_pos.ne'] <;> ring

theorem penalty_sound (j : ℕ) : node j*q (node j-1) ≤ (penalty j:ℝ)/(scale:ℝ) := by
  rw [le_div_iff₀ scale_pos,node_q]
  have hD : (0:ℝ) < 8192+j := by positivity
  have hD' : (0:ℝ) < 2+(j:ℝ)/4096 := by positivity
  calc
    _ = (ratio j:ℝ)*((scale:ℝ)*Real.log (1+(j:ℝ)/4096)) := by
      unfold node ratio
      push_cast
      field_simp [hD.ne',hD'.ne'] <;> ring
    _ ≤ _ := ratio_upper j

private theorem checked_sound (xs : List ℕ) (j : ℕ) (credit : ℤ)
    (hlen : j+xs.length ≤ 8193) (hcheck : checkRows xs j credit = true)
    (hcredit : (credit:ℝ)/(scale:ℝ) ≤ H (node j)) :
    ∀ k : ℕ, k < xs.length → ((xs.getD k 0:ℕ):ℝ)/(scale:ℝ) ≤ numerator (node (j+k)) := by
  induction xs generalizing j credit with
  | nil => simp
  | cons v xs ih =>
    simp only [checkRows,Bool.and_eq_true,decide_eq_true_eq] at hcheck
    simp only [List.length_cons] at hlen
    intro k hk
    cases k with
    | zero =>
      have hj : j ≤ 8192 := by omega
      have hb := node_bounds j hj
      have hcast : (v:ℝ)+(penalty j:ℝ) = (credit:ℝ) := by exact_mod_cast hcheck.1
      have hc : (v:ℝ)/(scale:ℝ)+(penalty j:ℝ)/(scale:ℝ) ≤ H (node j) := by
        rw [← add_div,hcast]
        exact hcredit
      simp only [List.getD_cons_zero,Nat.add_zero,numerator_eq hb.1 hb.2]
      linarith only [hc,penalty_sound j]
    | succ k =>
      have hk' : k < xs.length := by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using hk
      have hj : j < 8192 := by omega
      have hh : ((credit+leftStep j:ℤ):ℝ)/(scale:ℝ) ≤ H (node (j+1)) := by
        rw [Int.cast_add,add_div]
        linarith only [hcredit,leftStep_sound j hj]
      simpa only [List.getD_cons_succ,Nat.add_succ,Nat.succ_add,Nat.add_one] using
        ih (j+1) (credit+leftStep j) (by omega) hcheck.2 hh k hk'

/-- The original selected Q80 numerator at every one of the original
mesh endpoints, including 3 and 5, on the true normalized derivative. -/
theorem original_all_endpoints (j : Fin 8193) :
    (stored j.val:ℝ)/(2:ℝ)^80 ≤ -(node j.val)^2 * deriv upper (node j.val) := by
  have hstart : ((scale:ℤ):ℝ)/(scale:ℝ) ≤ H (node 0) := by
    simp [node,scale,H_eq_one (by norm_num : (1:ℝ)<3) le_rfl]
  have h := checked_sound derivativeLowerUnits 0 (scale:ℤ) (by rw [original_length]; decide)
    original_integer_links hstart j.val (by simpa only [original_length] using j.isLt)
  simpa only [stored,scale,Nat.cast_pow,Nat.cast_ofNat,Nat.zero_add,numerator] using h

set_option maxRecDepth 1000000 in
theorem original_last : stored 8192 = 39643994026485390435670 := by decide

theorem original_N5_pos : 0 < numerator 5 := by
  have h := original_all_endpoints (8192 : Fin 8193)
  change (stored 8192:ℝ)/(2:ℝ)^80 ≤ numerator (node 8192) at h
  rw [original_last,show node 8192 = 5 by norm_num [node]] at h
  exact lt_of_lt_of_le (by norm_num) h

theorem numerator_pos {s : ℝ} (ha : 1 < s) (hb : s ≤ 5) : 0 < numerator s :=
  original_N5_pos.trans_le (numerator_antitone ⟨ha,hb⟩ (by norm_num) hb)

/-- An upward-rounded terminal argument licenses the entire preceding
argument interval, including values at or below the transition. -/
theorem original_ceiling_lookup (j : Fin 8193) {s : ℝ} (hs : 1 < s) (hj : s ≤ node j.val) :
    (stored j.val:ℝ)/(2:ℝ)^80 ≤ numerator s := by
  have hn := node_bounds j.val (by omega)
  exact (original_all_endpoints j).trans
    (numerator_antitone ⟨hs,hj.trans hn.2⟩ ⟨by linarith [hn.1],hn.2⟩ hj)

end ImbalancedChen.P1OriginalFourthN8193
