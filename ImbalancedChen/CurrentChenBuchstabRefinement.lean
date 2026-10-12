import MathlibNt.SieveTheory.LiLiuBuchstabTailPropagation
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The current manuscript's global Buchstab refinement

This proves `11/20 <= buchstab s` for every `s >= 7/3`, for the actual
Buchstab function in the pinned `goldbach` dependency. The initial window
is the whole interval `[7/3,10/3]`. Its first part uses the genuine
logarithmic formula; its second part uses the actual delay integral and
the already proved global lower bound `1/2`. The delay integral then
propagates the lower barrier to the complete tail.

The logarithm estimate is the one-term specialization of mathlib's
proved lower Taylor sum. No sampled Buchstab values or monotonicity of
the Buchstab function are used. The conclusion is an independent input
to the adopted same-mask positive-fibre refinement, not a Chen mean or
the numerical certificate for that fibre.
-/

namespace ImbalancedChen

open Set MeasureTheory LiLiuPrereqBuchstab
open scoped Interval

noncomputable section

/-- The first term of the proved logarithm expansion gives the rational
lower bound used throughout the initial Buchstab window. -/
private theorem currentChen_log_rational_lower {x : ℝ} (hx : 1 ≤ x) :
    2 * ((x - 1) / (x + 1)) ≤ Real.log x := by
  let z : ℝ := (x - 1) / (x + 1)
  have hxp : 0 < x + 1 := by linarith
  have hz : 0 ≤ z := div_nonneg (by linarith) hxp.le
  have hz₁ : z < 1 := by
    apply (div_lt_iff₀ hxp).mpr
    linarith
  have he : (1 + z) / (1 - z) = x := by
    apply (div_eq_iff (show 1 - z ≠ 0 by linarith)).mpr
    dsimp [z]
    field_simp [hxp.ne'] <;> ring
  have hl := Real.sum_range_le_log_div hz hz₁ 1
  rw [he] at hl
  norm_num [Finset.sum_range_succ] at hl
  dsimp [z] at hl
  linarith only [hl]

/-- The first piece of the full starting window. The quadratic estimate
uses both endpoints of `[7/3,3]`, without a monotonicity assertion. -/
theorem currentChen_buchstab_lower_first_segment {s : ℝ}
    (hs : (7 : ℝ) / 3 ≤ s) (hs₃ : s ≤ 3) :
    (11 : ℝ) / 20 ≤ buchstab s := by
  have hs₀ : 0 < s := by linarith
  have hlog : 2 * ((s - 2) / s) ≤ Real.log (s - 1) := by
    simpa only [sub_sub, sub_add_cancel, show (1 : ℝ) + 1 = 2 by norm_num] using
      currentChen_log_rational_lower (x := s - 1) (by linarith)
  have hlog' : 2 * (s - 2) ≤ Real.log (s - 1) * s := by
    apply (div_le_iff₀ hs₀).mp
    simpa only [mul_div_assoc] using hlog
  have hquadratic : (11 : ℝ) / 20 * s ^ 2 ≤ 3 * s - 4 := by
    have hinterval : 0 ≤ (s - (7 : ℝ) / 3) * (3 - s) :=
      mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr hs₃)
    nlinarith only [hinterval, hs]
  rw [buchstab_eq_log_div (by linarith) hs₃]
  apply (le_div_iff₀ hs₀).mpr
  apply (mul_le_mul_iff_right₀ hs₀).mp
  nlinarith only [hquadratic, hlog']

/-- The transition segment is paid by the existing global `1/2` bound
inside the true Buchstab delay integral rebased at `3`. -/
theorem currentChen_buchstab_lower_transition {s : ℝ}
    (hs : 3 ≤ s) (hs₁₀ : s ≤ (10 : ℝ) / 3) :
    (11 : ℝ) / 20 ≤ buchstab s := by
  have hc : Continuous (fun t : ℝ => buchstab (t - 1)) :=
    continuous_buchstab.comp (continuous_id.sub continuous_const)
  have hi := intervalIntegral.integral_mono_on hs
    (intervalIntegrable_const :
      IntervalIntegrable (fun _ : ℝ => (1 / 2 : ℝ)) volume 3 s)
    (hc.intervalIntegrable 3 s)
    (fun t ht => one_half_le_buchstab (by linarith [ht.1] : 1 ≤ t - 1))
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hi
  have he := buchstab_weighted_sub_eq_integral (a := 3) (by norm_num) hs
  have hthree := buchstab_eq_log_div (u := 3) (by norm_num) (by norm_num)
  norm_num at hthree
  have hlog₂ : (2 : ℝ) / 3 ≤ Real.log 2 := by
    have h := currentChen_log_rational_lower (x := 2) (by norm_num)
    norm_num at h
    exact h
  have hs₀ : 0 < s := by linarith
  apply (mul_le_mul_iff_left₀ hs₀).mp
  nlinarith only [hi, he, hthree, hlog₂, hs₁₀]

/-- A constant lower barrier on a complete unit interval propagates to
the full tail of the actual Buchstab function. This is the lower-bound
counterpart of the pinned dependency's `buchstab_upper_on_tail`.
The later global refinement below supplies its entire base interval. -/
theorem currentChen_buchstab_lower_on_tail {a L : ℝ} (ha : 2 ≤ a)
    (hbase : ∀ u ∈ Icc a (a + 1), L ≤ buchstab u) :
    ∀ u : ℝ, a ≤ u → L ≤ buchstab u := by
  have hstage : ∀ n : ℕ, ∀ u : ℝ, a ≤ u → u ≤ a + (n : ℝ) + 1 →
      L ≤ buchstab u := by
    intro n
    induction n with
    | zero =>
      intro u hu hub
      exact hbase u ⟨hu, by simpa using hub⟩
    | succ n ih =>
      intro u hu hub
      by_cases hsmall : u ≤ a + 1
      · exact hbase u ⟨hu, hsmall⟩
      have hlu : a + 1 ≤ u := (lt_of_not_ge hsmall).le
      have hc : Continuous (fun t : ℝ => buchstab (t - 1)) :=
        continuous_buchstab.comp (continuous_id.sub continuous_const)
      have hi := intervalIntegral.integral_mono_on hlu
        (intervalIntegrable_const :
          IntervalIntegrable (fun _ : ℝ => L) volume (a + 1) u)
        (hc.intervalIntegrable (a + 1) u)
        (fun t ht => ih (t - 1) (by linarith [ht.1]) (by
          push_cast at hub
          linarith [ht.2]))
      simp only [intervalIntegral.integral_const, smul_eq_mul] at hi
      have he := buchstab_weighted_sub_eq_integral (a := a + 1) (by linarith) hlu
      have hb := hbase (a + 1) ⟨by linarith, le_rfl⟩
      have hp := mul_le_mul_of_nonneg_left hb (show 0 ≤ a + 1 by linarith)
      have hup : 0 < u := by linarith
      apply (mul_le_mul_iff_left₀ hup).mp
      nlinarith only [hi, he, hp]
  intro u hu
  obtain ⟨n, hn⟩ := exists_nat_gt (u - a)
  exact hstage n u hu (by linarith)

/-- The frozen manuscript's `lem:current-omega-refinement`, with its
literal cutoff and constant and no analytic estimate left as a premise. -/
theorem currentChen_buchstab_eleven_twentieths {s : ℝ}
    (hs : (7 : ℝ) / 3 ≤ s) :
    (11 : ℝ) / 20 ≤ LiLiuPrereqBuchstab.buchstab s := by
  apply currentChen_buchstab_lower_on_tail (a := (7 : ℝ) / 3) (by norm_num) _ s hs
  intro u hu
  by_cases hthree : u ≤ 3
  · exact currentChen_buchstab_lower_first_segment hu.1 hthree
  · exact currentChen_buchstab_lower_transition (le_of_lt (lt_of_not_ge hthree))
      (by linarith [hu.2])

end

end ImbalancedChen
