import ImbalancedChen.P5ZU1011OriginalSixteenTightMinimumDiagonal

/-!
# A genuine fixed integrable domination constant for the tight program

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

For EVERY generated box and every positive Buchstab order, queryspan<=6
and the proved omega remainder give omegaUpper<=3004. The original lower
coordinate a supplies costBound=3004*k/a and weightBound=(1/a)^4. Both
computed weighted endpoints lie in [0,costBound*weightBound], independently
of policy eligibility and independently of the box meeting the source.
These are actual-program bounds, not a DCT domination premise.
-/

namespace ImbalancedChen.P5Z.U1011OriginalSixteenTightUniformBounds

noncomputable section

open U11Integral U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSixteenRationalGridGeometry
open U1011OriginalSixteenRationalIntegralCertificates (weightLower weightUpper grid_lo_pos grid_hi_pos)
open U1011OriginalSixteenTightRationalIntegralCertificates
open OriginalSixteenTightSwitchedBoxes
open OriginalSixteenSwitchedBoxBounds (k zLower)
open scoped BigOperators

def costBound : ℚ := 3004 * k / OriginalSixteenSwitchedBoxBounds.a
def weightBound : ℚ := (1 / U1011OriginalSixteenRationalGridGeometry.a) ^ 4
def densityBound : ℚ := costBound * weightBound

theorem costBound_nonneg : 0 ≤ costBound := by norm_num [costBound, k, OriginalSixteenSwitchedBoxBounds.a]
theorem weightBound_nonneg : 0 ≤ weightBound := by unfold weightBound; positivity
theorem densityBound_nonneg : 0 ≤ densityBound := mul_nonneg costBound_nonneg weightBound_nonneg

theorem generated_omegaUpper_le (m : ℕ) (hm : 0 < m) (B : Box) : omegaUpper m B ≤ 3004 := by
  have hw := (omega_width m hm B).2
  have hl := (omegaLower_range m hm B).2
  have hq := query_valid B
  have hmQ : (1 : ℚ) ≤ m := by exact_mod_cast (Nat.succ_le_of_lt hm)
  have hdiv : (3000 : ℚ) / (m : ℚ) ≤ 3000 := div_le_self (by norm_num) hmQ
  linarith only [hw, hl, hq.1, hq.2.2, hdiv]

theorem switched_upper_uniform (m : ℕ) (hm : 0 < m) (B : Box) :
    0 ≤ switchedUpper m B ∧ switchedUpper m B ≤ costBound := by
  have ha : (0 : ℚ) < OriginalSixteenSwitchedBoxBounds.a := by norm_num [OriginalSixteenSwitchedBoxBounds.a]
  have hk : (0 : ℚ) ≤ k := by norm_num [k]
  have hz : OriginalSixteenSwitchedBoxBounds.a ≤ zLower B := le_max_left _ _
  have hzp := ha.trans_le hz
  have hω0 : 0 ≤ omegaUpper m B := by
    have h := (omega_width m hm B).1
    have hL := (omegaLower_range m hm B).1
    linarith only [h, hL]
  have hωU := generated_omegaUpper_le m hm B
  constructor
  · exact div_nonneg (mul_nonneg hk hω0) hzp.le
  · have hh := (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hωU hk) hzp.le).trans
      (div_le_div_of_nonneg_left (mul_nonneg hk (by norm_num : (0 : ℚ) ≤ 3004)) ha hz)
    simpa only [switchedUpper, costBound, mul_comm k 3004] using hh

theorem generated_cost_bounds (n m : ℕ) (hm : 0 < m) (j : Index n) :
    0 ≤ max (0 : ℚ) (boxLower m (gridBox n j)) ∧
      max (0 : ℚ) (boxLower m (gridBox n j)) ≤ costBound ∧
      0 ≤ max (0 : ℚ) (boxUpper m (gridBox n j)) ∧
      max (0 : ℚ) (boxUpper m (gridBox n j)) ≤ costBound := by
  have hs := switched_upper_uniform m hm (gridBox n j)
  have hgap := (switched_width m hm (gridBox n j) (gridBox_valid n j)).1
  have hL : boxLower m (gridBox n j) ≤ switchedLower m (gridBox n j) :=
    Finset.min'_le _ _ (Finset.mem_insert_self _ _)
  have hU : boxUpper m (gridBox n j) ≤ switchedUpper m (gridBox n j) :=
    Finset.min'_le _ _ (Finset.mem_insert_self _ _)
  exact ⟨le_max_left _ _, max_le costBound_nonneg ((hL.trans (sub_nonneg.mp hgap)).trans hs.2),
    le_max_left _ _, max_le costBound_nonneg (hU.trans hs.2)⟩

theorem generated_weight_bounds (n : ℕ) (j : Index n) :
    0 ≤ weightLower n j ∧ weightLower n j ≤ weightUpper n j ∧
      0 ≤ weightUpper n j ∧ weightUpper n j ≤ weightBound := by
  have hLo := grid_lo_pos n j
  have hHi := grid_hi_pos n j
  have hL0 : 0 ≤ weightLower n j := Finset.prod_nonneg (fun i _ => (one_div_pos.mpr (hHi i)).le)
  have hU0 : 0 ≤ weightUpper n j := Finset.prod_nonneg (fun i _ => (one_div_pos.mpr (hLo i)).le)
  have hLU : weightLower n j ≤ weightUpper n j := by
    apply Finset.prod_le_prod (fun i _ => (one_div_pos.mpr (hHi i)).le)
    intro i hi
    exact one_div_le_one_div_of_le (hLo i) (gridBox_valid n j i)
  have hUB : weightUpper n j ≤ weightBound := by
    calc
      weightUpper n j ≤ ∏ _i : Fin 4, (1 / U1011OriginalSixteenRationalGridGeometry.a) := by
        apply Finset.prod_le_prod (fun i _ => (one_div_pos.mpr (hLo i)).le)
        intro i hi
        exact one_div_le_one_div_of_le (by norm_num [U1011OriginalSixteenRationalGridGeometry.a])
          (gridBox_corner_bounds n j i).1
      _ = weightBound := by simp [weightBound]
  exact ⟨hL0, hLU, hU0, hUB⟩

theorem generated_density_bounds (n m : ℕ) (hm : 0 < m) (j : Index n) :
    0 ≤ densityLower n m j ∧ densityLower n m j ≤ densityBound ∧
      0 ≤ densityUpper n m j ∧ densityUpper n m j ≤ densityBound := by
  have hc := generated_cost_bounds n m hm j
  have hw := generated_weight_bounds n j
  exact ⟨mul_nonneg hc.1 hw.1,
    mul_le_mul hc.2.1 (hw.2.1.trans hw.2.2.2) hw.1 costBound_nonneg,
    mul_nonneg hc.2.2.1 hw.2.2.1,
    mul_le_mul hc.2.2.2 hw.2.2.2 hw.2.2.1 costBound_nonneg⟩

end

end ImbalancedChen.P5Z.U1011OriginalSixteenTightUniformBounds
