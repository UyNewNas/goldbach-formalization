import ImbalancedChen.P5U7OriginalOmegaIntegral
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
The actual Buchstab function is 1-Lipschitz on the complete original U7
argument interval [1,132/59], including the s=2 seam. Proof uses exact
finite differences of both actual formulas and elementary logarithm
inequalities; no differentiability, Lipschitz or oscillation supplier is
assumed. This is a new analytic primitive for rational-cover convergence.
-/

namespace ImbalancedChen

noncomputable section

open Set LiLiuPrereqBuchstab

/-- Elementary scalar logarithm control on the fixed lower band one. -/
theorem p5U7_abs_log_sub_log_le {p q : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q) :
    |Real.log p - Real.log q| ≤ |p - q| := by
  have hordered : ∀ p q : ℝ, 1 ≤ p → 1 ≤ q → p ≤ q →
      |Real.log p - Real.log q| ≤ |p - q| := by
    intro p q hp hq hpq
    have hp0 : 0 < p := zero_lt_one.trans_le hp
    have hq0 : 0 < q := zero_lt_one.trans_le hq
    have hm := Real.log_le_log hp0 hpq
    have hlog := Real.log_le_sub_one_of_pos (div_pos hq0 hp0)
    rw [Real.log_div hq0.ne' hp0.ne'] at hlog
    have heq : q / p - 1 = (q - p) / p := by
      field_simp [hp0.ne']
      <;> ring
    have hscale : q / p - 1 ≤ q - p := by
      rw [heq]
      exact div_le_self (sub_nonneg.mpr hpq) hp
    rw [abs_of_nonpos (sub_nonpos.mpr hm), abs_of_nonpos (sub_nonpos.mpr hpq)]
    linarith only [hlog, hscale]
  rcases le_total p q with h | h
  · exact hordered p q hp hq h
  · simpa only [abs_sub_comm] using hordered q p hq hp h

/-- Exact reciprocal finite difference with its positive-band square
denominator. This is used with a=1 and a=2 on the two Buchstab pieces. -/
theorem p5U7_abs_reciprocal_sub_le {a s t : ℝ} (ha : 0 < a)
    (hs : a ≤ s) (ht : a ≤ t) :
    |1 / s - 1 / t| ≤ |s - t| / a ^ 2 := by
  have hs0 : 0 < s := ha.trans_le hs
  have ht0 : 0 < t := ha.trans_le ht
  have heq : 1 / s - 1 / t = (t - s) / (s * t) := by
    field_simp [hs0.ne', ht0.ne']
    <;> ring
  have hprod : a ^ 2 ≤ s * t := by
    simpa only [pow_two] using mul_le_mul hs ht ha.le hs0.le
  rw [heq, abs_div, abs_of_pos (mul_pos hs0 ht0), abs_sub_comm t s]
  exact div_le_div_of_nonneg_left (abs_nonneg _) (sq_pos_of_pos ha) hprod

theorem p5U7_buchstab_first_abs_sub_le {s t : ℝ}
    (hs : s ∈ Icc (1 : ℝ) 2) (ht : t ∈ Icc (1 : ℝ) 2) :
    |buchstab s - buchstab t| ≤ |s - t| := by
  rw [buchstab_eq_one_div hs.1 hs.2, buchstab_eq_one_div ht.1 ht.2]
  simpa only [one_pow, div_one] using
    p5U7_abs_reciprocal_sub_le (a := 1) zero_lt_one hs.1 ht.1

/-- The second actual piece has the same constant one. The logarithmic
term costs half the distance, and the reciprocal term costs the other half. -/
theorem p5U7_buchstab_second_abs_sub_le {s t : ℝ}
    (hs : s ∈ Icc (2 : ℝ) (132 / 59))
    (ht : t ∈ Icc (2 : ℝ) (132 / 59)) :
    |buchstab s - buchstab t| ≤ |s - t| := by
  have hs0 : 0 < s := by linarith only [hs.1]
  have ht0 : 0 < t := by linarith only [ht.1]
  have hlog : |Real.log (s - 1) - Real.log (t - 1)| ≤ |s - t| := by
    have h := p5U7_abs_log_sub_log_le
      (show 1 ≤ s - 1 by linarith only [hs.1])
      (show 1 ≤ t - 1 by linarith only [ht.1])
    have harg : (s - 1) - (t - 1) = s - t := by ring
    simpa only [harg] using h
  have hrec : |1 / s - 1 / t| ≤ |s - t| / 4 := by
    have h := p5U7_abs_reciprocal_sub_le (a := 2) (by norm_num) hs.1 ht.1
    norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num] at h
    exact h
  have hn0 : 0 ≤ 1 + Real.log (t - 1) := by
    have h := Real.log_nonneg (show 1 ≤ t - 1 by linarith only [ht.1])
    linarith only [h]
  have hn2 : |1 + Real.log (t - 1)| ≤ 2 := by
    rw [abs_of_nonneg hn0]
    have h := Real.log_le_sub_one_of_pos (show 0 < t - 1 by linarith only [ht.1])
    linarith only [h, ht.2]
  have heq :
      (1 + Real.log (s - 1)) / s - (1 + Real.log (t - 1)) / t =
      (Real.log (s - 1) - Real.log (t - 1)) / s +
        (1 + Real.log (t - 1)) * (1 / s - 1 / t) := by
    field_simp [hs0.ne', ht0.ne']
    <;> ring
  rw [buchstab_eq_log_div hs.1 (by linarith only [hs.2] : s ≤ 3),
    buchstab_eq_log_div ht.1 (by linarith only [ht.2] : t ≤ 3), heq]
  calc
    _ ≤ |(Real.log (s - 1) - Real.log (t - 1)) / s| +
        |(1 + Real.log (t - 1)) * (1 / s - 1 / t)| := abs_add _ _
    _ = |Real.log (s - 1) - Real.log (t - 1)| / s +
        |1 + Real.log (t - 1)| * |1 / s - 1 / t| := by
      rw [abs_div, abs_of_pos hs0, abs_mul]
    _ ≤ |s - t| / 2 + 2 * (|s - t| / 4) := by
      apply add_le_add
      · exact (div_le_div_of_nonneg_right hlog hs0.le).trans
          (div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) hs.1)
      · exact mul_le_mul hn2 hrec (abs_nonneg _) (by norm_num)
    _ = |s - t| := by ring

/-- Complete original argument interval, with a genuine cross-seam
estimate. The two segment lengths add exactly when 2 lies between s,t. -/
theorem p5U7_buchstab_abs_sub_le {s t : ℝ}
    (hs : s ∈ Icc (1 : ℝ) (132 / 59))
    (ht : t ∈ Icc (1 : ℝ) (132 / 59)) :
    |buchstab s - buchstab t| ≤ |s - t| := by
  have hordered : ∀ s t : ℝ,
      s ∈ Icc (1 : ℝ) (132 / 59) → t ∈ Icc (1 : ℝ) (132 / 59) → s ≤ t →
      |buchstab s - buchstab t| ≤ |s - t| := by
    intro s t hs ht hst
    by_cases ht2 : t ≤ 2
    · exact p5U7_buchstab_first_abs_sub_le ⟨hs.1, hst.trans ht2⟩ ⟨ht.1, ht2⟩
    by_cases hs2 : 2 ≤ s
    · exact p5U7_buchstab_second_abs_sub_le ⟨hs2, hs.2⟩ ⟨hs2.trans hst, ht.2⟩
    have hs2' : s ≤ 2 := (lt_of_not_ge hs2).le
    have ht2' : 2 ≤ t := (lt_of_not_ge ht2).le
    have hleft := p5U7_buchstab_first_abs_sub_le ⟨hs.1, hs2'⟩
      (show (2 : ℝ) ∈ Icc (1 : ℝ) 2 by norm_num)
    have hright := p5U7_buchstab_second_abs_sub_le
      (show (2 : ℝ) ∈ Icc (2 : ℝ) (132 / 59) by norm_num) ⟨ht2', ht.2⟩
    calc
      _ ≤ |buchstab s - buchstab 2| + |buchstab 2 - buchstab t| := abs_sub_le _ _ _
      _ ≤ |s - 2| + |2 - t| := add_le_add hleft hright
      _ = |s - t| := by
        rw [abs_of_nonpos (sub_nonpos.mpr hs2'),
          abs_of_nonpos (sub_nonpos.mpr ht2'), abs_of_nonpos (sub_nonpos.mpr hst)]
        ring
  rcases le_total s t with h | h
  · exact hordered s t hs ht h
  · simpa only [abs_sub_comm] using hordered t s ht hs h

theorem p5U7_buchstab_lipschitzOn_original :
    LipschitzOnWith 1 buchstab (Icc (1 : ℝ) (132 / 59)) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro s hs t ht
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using
    p5U7_buchstab_abs_sub_le hs ht

end

end ImbalancedChen
