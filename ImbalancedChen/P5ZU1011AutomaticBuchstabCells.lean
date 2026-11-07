import ImbalancedChen.P5ZU1011AutomaticBuchstabWidthRate

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
True finite rational whole-cell omega enclosures from the automatic node
producer, with a uniform explicit 1500/m gap on the original [1,8] window.
Both query denominators are certified endpoints; no actual omega query
remains in either rational output. No cell-bound or node-data premise.
-/

namespace ImbalancedChen.P5Z.AutomaticBuchstabCells

noncomputable section

open Set LiLiuPrereqBuchstab
open Certificates.P2BuchstabRationalSemantics
open AutomaticBuchstabNodes AutomaticBuchstabWidthStep AutomaticBuchstabWidthRate

def cellLower (m k : ℕ) : ℚ := max 0 ((node m k).lower / grid m (k + 1))
def cellUpper (m k : ℕ) : ℚ := (node m (k + 1)).upper / grid m k

theorem grid_ge_one (m k : ℕ) (hm : 0 < m) : (1 : ℚ) ≤ grid m k := by
  unfold grid
  have h : (0 : ℚ) ≤ (k : ℚ) / (m : ℚ) := div_nonneg (Nat.cast_nonneg k) (by positivity)
  linarith only [h]

theorem grid_le_next (m k : ℕ) (hm : 0 < m) : grid m k ≤ grid m (k + 1) := by
  have hh := grid_step m k
  have hp : (0 : ℚ) ≤ 1 / m := by positivity
  linarith only [hh, hp]

/-- Literal actual omega is enclosed on the COMPLETE closed mesh cell.
The left lower psi uses the RIGHT denominator, and vice versa. -/
theorem actual_cell_bounds (m k : ℕ) (hm : 0 < m) {s : ℝ}
    (hs : s ∈ Icc (grid m k : ℝ) (grid m (k + 1) : ℝ)) :
    (cellLower m k : ℝ) ≤ buchstab s ∧ buchstab s ≤ (cellUpper m k : ℝ) := by
  have ha1 : (1 : ℝ) ≤ (grid m k : ℝ) := by exact_mod_cast grid_ge_one m k hm
  have hb1 : (1 : ℝ) ≤ (grid m (k + 1) : ℝ) := by exact_mod_cast grid_ge_one m (k + 1) hm
  have ha0 : (0 : ℝ) < (grid m k : ℝ) := zero_lt_one.trans_le ha1
  have hb0 : (0 : ℝ) < (grid m (k + 1) : ℝ) := zero_lt_one.trans_le hb1
  have hs1 : 1 ≤ s := ha1.trans hs.1
  have hω0 := buchstab_nonneg hs1
  have hL := (actual_node_bounds m k hm).1
  have hU := (actual_node_bounds m (k + 1) hm).2
  have hmL := weighted_mono ha1 hs.1
  have hmU := weighted_mono hs1 hs.2
  have hlow : ((node m k).lower : ℝ) / (grid m (k + 1) : ℝ) ≤ buchstab s := by
    apply (div_le_iff₀ hb0).mpr
    have hh := mul_le_mul_of_nonneg_right hs.2 hω0
    change ((node m k).lower : ℝ) ≤ buchstab s * (grid m (k + 1) : ℝ)
    dsimp only [weighted] at hL hmL
    nlinarith only [hL, hmL, hh]
  have hupp : buchstab s ≤ ((node m (k + 1)).upper : ℝ) / (grid m k : ℝ) := by
    apply (le_div_iff₀ ha0).mpr
    have hh := mul_le_mul_of_nonneg_right hs.1 hω0
    dsimp only [weighted] at hU hmU
    nlinarith only [hU, hmU, hh]
  simp only [cellLower, cellUpper, Rat.cast_max, Rat.cast_zero, Rat.cast_div]
  exact ⟨max_le hω0 hlow, hupp⟩

/-- The actual endpoint-directed cell coefficients have uniformly small
width. Their initial zero clamp is safe and can only reduce this width. -/
theorem actual_cell_width (m k : ℕ) (hm : 0 < m) (hk : k + 1 ≤ 7 * m) :
    0 ≤ cellUpper m k - cellLower m k ∧
      cellUpper m k - cellLower m k ≤ 1500 / (m : ℚ) := by
  let a : ℝ := grid m k
  let b : ℝ := grid m (k + 1)
  have ha1 : 1 ≤ a := by exact_mod_cast grid_ge_one m k hm
  have hab : a ≤ b := by exact_mod_cast grid_le_next m k hm
  have hb1 : 1 ≤ b := ha1.trans hab
  have ha0 : 0 < a := zero_lt_one.trans_le ha1
  have hb0 : 0 < b := zero_lt_one.trans_le hb1
  have hStep : b - a = 1 / (m : ℝ) := by exact_mod_cast grid_step m k
  have hErrA := original_window_node_errors m k hm (by omega)
  have hErrB := original_window_node_errors m (k + 1) hm hk
  have hInc := weighted_increment_all ha1 hab
  have hNodesA := actual_node_bounds m k hm
  have hNodesB := actual_node_bounds m (k + 1) hm
  have hCross0 : 0 ≤ ((node m (k + 1)).upper : ℝ) - ((node m k).lower : ℝ) := by
    linarith only [hNodesA.1, hNodesB.2, hInc.1]
  have hCross : ((node m (k + 1)).upper : ℝ) - ((node m k).lower : ℝ) ≤ 1457 / (m : ℝ) := by
    linarith only [hErrA.2.1, hErrB.2.2.2, hInc.2, hStep]
  have hFirst : (((node m (k + 1)).upper : ℝ) - ((node m k).lower : ℝ)) / a ≤
      1457 / (m : ℝ) := (div_le_self hCross0 ha1).trans hCross
  have hInv : 0 ≤ 1 / a - 1 / b := sub_nonneg.mpr (one_div_le_one_div_of_le ha0 hab)
  have hLowerA : ((node m k).lower : ℝ) ≤ a := by
    have hh := mul_le_mul_of_nonneg_left (buchstab_le_one ha1) ha0.le
    dsimp only [weighted] at hNodesA
    nlinarith only [hNodesA.1, hh]
  have hSecond : ((node m k).lower : ℝ) * (1 / a - 1 / b) ≤ 1 / (m : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hLowerA hInv
    have heq : a * (1 / a - 1 / b) = (b - a) / b := by
      field_simp [ha0.ne', hb0.ne']
      <;> ring
    rw [heq] at hh
    exact hh.trans ((div_le_self (sub_nonneg.mpr hab) hb1).trans_eq hStep)
  have hRaw : ((node m (k + 1)).upper : ℝ) / a - ((node m k).lower : ℝ) / b ≤
      1458 / (m : ℝ) := by
    have heq : ((node m (k + 1)).upper : ℝ) / a - ((node m k).lower : ℝ) / b =
        (((node m (k + 1)).upper : ℝ) - ((node m k).lower : ℝ)) / a +
          ((node m k).lower : ℝ) * (1 / a - 1 / b) := by ring
    rw [heq]
    linarith only [hFirst, hSecond]
  have hClamp : ((node m k).lower : ℝ) / b ≤ (cellLower m k : ℝ) := by
    simp only [cellLower, Rat.cast_max, Rat.cast_zero, Rat.cast_div]
    exact le_max_right _ _
  have hBound := actual_cell_bounds m k hm (s := a) ⟨le_rfl, hab⟩
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hR0 : (0 : ℝ) ≤ (cellUpper m k : ℝ) - (cellLower m k : ℝ) := by
    linarith only [hBound.1, hBound.2]
  have hR1 : (cellUpper m k : ℝ) - (cellLower m k : ℝ) ≤ 1500 / (m : ℝ) := by
    simp only [cellUpper, Rat.cast_div]
    change ((node m (k + 1)).upper : ℝ) / a - (cellLower m k : ℝ) ≤ _
    have hh : (1458 : ℝ) / m ≤ 1500 / m :=
      div_le_div_of_nonneg_right (by norm_num) hmR.le
    linarith only [hRaw, hClamp, hh]
  exact ⟨by exact_mod_cast hR0, by exact_mod_cast hR1⟩

end

end ImbalancedChen.P5Z.AutomaticBuchstabCells
