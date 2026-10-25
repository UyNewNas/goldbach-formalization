import ImbalancedChen.P5ZU1011AutomaticBuchstabWidthStep

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
Finite unit-delay depth propagation for the ACTUAL deterministic rational
nodes. Each unit window costs C->3C+2, beginning with exact width zero.
Depth six covers the complete original [1,8] query window and gives the
explicit uniform width 728/m. No node-error or propagated-rate premise.
-/

namespace ImbalancedChen.P5Z.AutomaticBuchstabWidthRate

noncomputable section

open Certificates.P2BuchstabRationalSemantics
open AutomaticBuchstabNodes AutomaticBuchstabWidthStep

def depthConstant : ℕ → ℚ
  | 0 => 0
  | d + 1 => 3 * depthConstant d + 2

theorem depthConstant_nonneg (d : ℕ) : 0 ≤ depthConstant d := by
  induction d with
  | zero => exact le_rfl
  | succ d ih => change 0 ≤ 3 * depthConstant d + 2; positivity

private theorem extend_one_unit (m base : ℕ) (hm : 0 < m) (hbase : m ≤ base)
    (C : ℚ) (hC : 0 ≤ C) (hprev : ∀ k : ℕ, k ≤ base → width m k ≤ C / m) :
    ∀ k : ℕ, k ≤ base + m → width m k ≤ (3 * C + 2) / m := by
  have hmQ : (0 : ℚ) < m := by exact_mod_cast hm
  have hm0 : (m : ℚ) ≠ 0 := ne_of_gt hmQ
  let inc : ℚ := (2 * C + 2) / (m : ℚ) ^ 2
  have hinc0 : 0 ≤ inc := by dsimp [inc]; positivity
  have hincEq : (1 / (m : ℚ)) * (C / m + C / m + 2 / m) = inc := by
    dsimp [inc]
    field_simp [hm0]
    <;> ring
  have hwithin : ∀ t : ℕ, t ≤ m → width m (base + t) ≤ C / m + (t : ℚ) * inc := by
    intro t
    induction t with
    | zero =>
        intro _
        simpa only [Nat.add_zero, Nat.cast_zero, zero_mul, add_zero] using hprev base le_rfl
    | succ t ih =>
        intro ht
        have ht0 : t ≤ m := by omega
        have hIH := ih ht0
        have hstep := actual_width_step m (base + t) hm (by omega)
        have hleft := hprev (base + t - m) (by omega)
        have hright := hprev (base + t - m + 1) (by omega)
        have hh := mul_le_mul_of_nonneg_left (add_le_add_right (add_le_add hleft hright) (2 / (m : ℚ)))
          (show (0 : ℚ) ≤ 1 / m by positivity)
        rw [hincEq] at hh
        have hnext : base + (t + 1) = base + t + 1 := by omega
        rw [hnext]
        push_cast
        linarith only [hIH, hstep, hh]
  intro k hk
  by_cases hsmall : k ≤ base
  · have hh := hprev k hsmall
    have hbudget : C / (m : ℚ) ≤ (3 * C + 2) / m :=
      div_le_div_of_nonneg_right (by linarith only [hC]) hmQ.le
    exact hh.trans hbudget
  · have hbk : base ≤ k := (lt_of_not_ge hsmall).le
    have ht : k - base ≤ m := by omega
    have hh := hwithin (k - base) ht
    rw [Nat.add_sub_of_le hbk] at hh
    have htQ : ((k - base : ℕ) : ℚ) ≤ m := by exact_mod_cast ht
    have hspan := mul_le_mul_of_nonneg_right htQ hinc0
    have htotal : C / (m : ℚ) + (m : ℚ) * inc = (3 * C + 2) / m := by
      dsimp [inc]
      field_simp [hm0]
      <;> ring
    linarith only [hh, hspan, htotal]

/-- Uniform true node width, by a finite number of UNIT delay windows.
The depth and mesh are arbitrary; the function values remain actual. -/
theorem actual_width_depth (d m : ℕ) (hm : 0 < m) :
    ∀ k : ℕ, k ≤ (d + 1) * m → width m k ≤ depthConstant d / m := by
  induction d with
  | zero =>
      intro k hk
      have hkm : k ≤ m := by simpa only [zero_add, one_mul] using hk
      rw [width_initial m k hm hkm]
      simp only [depthConstant, zero_div, le_refl]
  | succ d ih =>
      have hbase : m ≤ (d + 1) * m := by
        have hh := Nat.mul_le_mul_right m (show 1 ≤ d + 1 by omega)
        simpa only [one_mul] using hh
      have hh := extend_one_unit m ((d + 1) * m) hm hbase (depthConstant d)
        (depthConstant_nonneg d) ih
      intro k hk
      have hlimit : k ≤ (d + 1) * m + m := by
        nlinarith only [hk]
      simpa only [depthConstant] using hh k hlimit

theorem depth_six : depthConstant 6 = 728 := by norm_num [depthConstant]

/-- Complete actual original query window through 8. No numerical
instance is computed; 728 is the symbolic depth-six propagation constant. -/
theorem original_window_width (m k : ℕ) (hm : 0 < m) (hk : k ≤ 7 * m) :
    0 ≤ width m k ∧ width m k ≤ 728 / (m : ℚ) := by
  have hh := actual_width_depth 6 m hm k (by simpa using hk)
  rw [depth_six] at hh
  exact ⟨width_nonneg m k hm, hh⟩

/-- Both directed errors at each actual generated weighted node are paid
by the same uniform rational constant, without assumed node enclosures. -/
theorem original_window_node_errors (m k : ℕ) (hm : 0 < m) (hk : k ≤ 7 * m) :
    0 ≤ weighted (grid m k) - ((node m k).lower : ℝ) ∧
      weighted (grid m k) - ((node m k).lower : ℝ) ≤ 728 / (m : ℝ) ∧
      0 ≤ ((node m k).upper : ℝ) - weighted (grid m k) ∧
      ((node m k).upper : ℝ) - weighted (grid m k) ≤ 728 / (m : ℝ) := by
  have hh := actual_node_bounds m k hm
  have hW : ((node m k).upper : ℝ) - ((node m k).lower : ℝ) ≤ 728 / (m : ℝ) := by
    exact_mod_cast (original_window_width m k hm hk).2
  exact ⟨sub_nonneg.mpr hh.1, (by linarith only [hh.2, hW]),
    sub_nonneg.mpr hh.2, (by linarith only [hh.1, hW])⟩

end

end ImbalancedChen.P5Z.AutomaticBuchstabWidthRate
