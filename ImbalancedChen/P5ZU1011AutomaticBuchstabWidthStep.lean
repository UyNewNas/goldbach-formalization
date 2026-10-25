import ImbalancedChen.P5ZU1011AutomaticBuchstabNodes
import ImbalancedChen.P5ZU1011BuchstabTailLipschitz

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
Actual one-step quantitative width propagation for the deterministic
directed Buchstab node producer. The delayed interval's genuine weighted
increment and the exact denominator excess are both paid. No node-width,
quadrature-error or desired-node enclosure supplier is assumed.
-/

namespace ImbalancedChen.P5Z.AutomaticBuchstabWidthStep

noncomputable section

open Set LiLiuPrereqBuchstab
open Certificates.P2BuchstabRationalSemantics
open AutomaticBuchstabNodes U1011BuchstabTailLipschitz

def width (m k : ℕ) : ℚ := (node m k).upper - (node m k).lower

theorem width_nonneg (m k : ℕ) (hm : 0 < m) : 0 ≤ width m k := by
  have hh := actual_node_bounds m k hm
  have hr : (0 : ℝ) ≤ ((node m k).upper : ℝ) - ((node m k).lower : ℝ) := by
    linarith only [hh.1, hh.2]
  exact_mod_cast hr

theorem width_initial (m k : ℕ) (hm : 0 < m) (hk : k ≤ m) : width m k = 0 := by
  simp only [width, node_initial m k hm hk, sub_self]

/-- The actual weighted function has unit slope budget on the ENTIRE
delayed interval beginning at one, including the initial s=2 join. -/
theorem weighted_increment_all {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    0 ≤ weighted b - weighted a ∧ weighted b - weighted a ≤ b - a := by
  have hm := weighted_mono ha hab
  refine ⟨sub_nonneg.mpr hm, ?_⟩
  by_cases hb2 : b ≤ 2
  · rw [weighted_initial ha (hab.trans hb2), weighted_initial (ha.trans hab) hb2]
    linarith only [hab]
  by_cases ha2 : 2 ≤ a
  · exact (weighted_increment_bounds ha2 hab).2
  · have ha2' : a ≤ 2 := (lt_of_not_ge ha2).le
    have hb2' : 2 ≤ b := (lt_of_not_ge hb2).le
    have hh := (weighted_increment_bounds (s := 2) (by norm_num) hb2').2
    have htwo : weighted 2 = 1 := weighted_initial (by norm_num) (by norm_num)
    rw [weighted_initial ha ha2']
    change b * buchstab b - 1 ≤ b - a
    change (2 : ℝ) * buchstab 2 = 1 at htwo
    linarith only [hh, htwo, ha2']

private theorem delayed_rectangle_excess {a b lA uA lB uB : ℝ}
    (ha : 2 ≤ a) (hab : a ≤ b)
    (hA : lA ≤ weighted (a - 1) ∧ weighted (a - 1) ≤ uA)
    (hB : lB ≤ weighted (b - 1) ∧ weighted (b - 1) ≤ uB) :
    uB / (a - 1) - lA / (b - 1) ≤ (uA - lA) + (uB - lB) + 2 * (b - a) := by
  let A := a - 1
  let B := b - 1
  have hA1 : 1 ≤ A := by dsimp [A]; linarith only [ha]
  have hAB : A ≤ B := by dsimp [A, B]; linarith only [hab]
  have hB1 : 1 ≤ B := hA1.trans hAB
  have hA0 : 0 < A := zero_lt_one.trans_le hA1
  have hB0 : 0 < B := zero_lt_one.trans_le hB1
  have hinc := weighted_increment_all hA1 hAB
  have hgapA : 0 ≤ uA - lA := by linarith only [hA.1, hA.2]
  have hgapB : 0 ≤ uB - lB := by linarith only [hB.1, hB.2]
  have hcross0 : 0 ≤ uB - lA := by linarith only [hA.1, hB.2, hinc.1]
  have hcross : uB - lA ≤ (uA - lA) + (uB - lB) + (B - A) := by
    linarith only [hA.2, hB.1, hinc.2]
  have hψA : weighted A ≤ A := by
    have hh := mul_le_mul_of_nonneg_left (buchstab_le_one hA1) hA0.le
    simpa only [weighted, mul_one] using hh
  have hInv : 0 ≤ 1 / A - 1 / B :=
    sub_nonneg.mpr (one_div_le_one_div_of_le hA0 hAB)
  have hfirst : (uB - lA) / A ≤ (uA - lA) + (uB - lB) + (B - A) :=
    (div_le_self hcross0 hA1).trans hcross
  have hsecond : lA * (1 / A - 1 / B) ≤ B - A := by
    have hh := mul_le_mul_of_nonneg_right (hA.1.trans hψA) hInv
    have heq : A * (1 / A - 1 / B) = (B - A) / B := by
      field_simp [hA0.ne', hB0.ne']
      <;> ring
    rw [heq] at hh
    exact hh.trans (div_le_self (sub_nonneg.mpr hAB) hB1)
  have heq : uB / A - lA / B = (uB - lA) / A + lA * (1 / A - 1 / B) := by ring
  change uB / A - lA / B ≤ _
  rw [heq]
  dsimp [A, B] at hfirst hsecond
  linarith only [hfirst, hsecond]

theorem grid_delay (m k : ℕ) (hm : 0 < m) (hkm : m ≤ k) :
    grid m (k - m) = grid m k - 1 := by
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hm
  unfold grid
  rw [Nat.cast_sub hkm]
  field_simp [hm0]
  <;> ring

theorem grid_step (m k : ℕ) : grid m (k + 1) - grid m k = 1 / (m : ℚ) := by
  unfold grid
  simp only [Nat.cast_add, Nat.cast_one]
  ring

/-- Actual quantitative recurrence. Every predecessor width on the
right is from the deterministic producer, not a supplied analytic error.
This is the input to the subsequent finite delay-depth propagation. -/
theorem actual_width_step (m j : ℕ) (hm : 0 < m) (hjm : m ≤ j) :
    width m (j + 1) ≤ width m j + (1 / (m : ℚ)) *
      (width m (j - m) + width m (j - m + 1) + 2 / (m : ℚ)) := by
  have hmQ : (0 : ℚ) < m := by exact_mod_cast hm
  have hja : (2 : ℚ) ≤ grid m j := by
    have hjQ : (m : ℚ) ≤ j := by exact_mod_cast hjm
    have hh : (1 : ℚ) ≤ (j : ℚ) / (m : ℚ) :=
      (le_div_iff₀ hmQ).mpr (by simpa only [one_mul] using hjQ)
    unfold grid
    linarith only [hh]
  have hjb : grid m j ≤ grid m (j + 1) := by
    have hh := grid_step m j
    have hpos : (0 : ℚ) ≤ 1 / m := by positivity
    linarith only [hh, hpos]
  have hA := actual_node_bounds m (j - m) hm
  have hB := actual_node_bounds m (j - m + 1) hm
  have hDelayA : (grid m (j - m) : ℝ) = (grid m j : ℝ) - 1 := by
    exact_mod_cast grid_delay m j hm hjm
  have hDelayB : (grid m (j - m + 1) : ℝ) = (grid m (j + 1) : ℝ) - 1 := by
    have heq : j - m + 1 = j + 1 - m := by omega
    rw [heq]
    exact_mod_cast grid_delay m (j + 1) hm (by omega)
  rw [hDelayA] at hA
  rw [hDelayB] at hB
  have hExcess := delayed_rectangle_excess (a := (grid m j : ℝ)) (b := (grid m (j + 1) : ℝ))
    (by exact_mod_cast hja)
    (by exact_mod_cast hjb) hA hB
  have hExcessQ : (node m (j - m + 1)).upper / (grid m j - 1) -
      (node m (j - m)).lower / (grid m (j + 1) - 1) ≤
      width m (j - m) + width m (j - m + 1) + 2 / (m : ℚ) := by
    have hStepR : (grid m (j + 1) : ℝ) - (grid m j : ℝ) = 1 / (m : ℝ) := by
      exact_mod_cast grid_step m j
    have hh :
        ((node m (j - m + 1)).upper : ℝ) / ((grid m j : ℝ) - 1) -
        ((node m (j - m)).lower : ℝ) / ((grid m (j + 1) : ℝ) - 1) ≤
        (width m (j - m) : ℝ) + (width m (j - m + 1) : ℝ) + 2 / (m : ℝ) := by
      simp only [width, Rat.cast_sub]
      linarith only [hExcess, hStepR]
    exact_mod_cast hh
  have hnode := node_step m (j + 1) hm (by omega)
  have hpred : j + 1 - 1 = j := by omega
  unfold width at ⊢
  rw [hnode]
  simp only [hpred]
  have hh := mul_le_mul_of_nonneg_left hExcessQ (by positivity : (0 : ℚ) ≤ 1 / m)
  simp only [width] at hh
  linarith only [hh]

end

end ImbalancedChen.P5Z.AutomaticBuchstabWidthStep
