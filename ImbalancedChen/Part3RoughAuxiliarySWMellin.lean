import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Order.Interval.Finset.Nat

/-!
# Mellin phase variation on a short interval

Multiplying a bounded complex profile by the phase `n ^ (I * t)` increases the
partial summation factor by at most `|t|` on the intervals used by the rough chart.
-/

namespace ImbalancedChen.Part3

open scoped BigOperators

private theorem mellinPhase_norm_eq_one (t x : ℝ) (hx : 0 < x) :
    ‖(x : ℂ) ^ (Complex.I * (t : ℂ))‖ = 1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp [Complex.mul_re]

private theorem mellinPhase_step_norm_le (t : ℝ) {m n : ℕ}
    (hm : 0 < m) (hmn : m ≤ n) :
    ‖((n + 1 : ℕ) : ℂ) ^ (Complex.I * (t : ℂ)) -
      (n : ℂ) ^ (Complex.I * (t : ℂ))‖ ≤ |t| / (m : ℝ) := by
  let r : ℂ := Complex.I * (t : ℂ)
  have hm' : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hmn' : (m : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hmn
  have hderiv (x : ℝ) (hx : (n : ℝ) ≤ x) :
      HasDerivAt (fun y : ℝ => (y : ℂ) ^ r) (r * (x : ℂ) ^ (r - 1)) x :=
    (Complex.hasStrictDerivAt_cpow_const
      (Complex.ofReal_mem_slitPlane.mpr (hm'.trans_le (hmn'.trans hx)))).hasDerivAt.comp_ofReal
  have hbound (x : ℝ) (hx : (n : ℝ) ≤ x) :
      ‖r * (x : ℂ) ^ (r - 1)‖ ≤ |t| / (m : ℝ) := by
    have hx' : 0 < x := hm'.trans_le (hmn'.trans hx)
    have hr : r.re = 0 := by simp [r, Complex.mul_re]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx', Complex.sub_re, hr,
      Complex.one_re, zero_sub, Real.rpow_neg_one, show ‖r‖ = |t| by simp [r], ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left (abs_nonneg t) hm' (hmn'.trans hx)
  have hstep := norm_image_sub_le_of_norm_deriv_le_segment'
    (a := (n : ℝ)) (b := (n : ℝ) + 1)
    (fun x hx => (hderiv x hx.1).hasDerivWithinAt)
    (fun x hx => hbound x hx.1)
    ((n : ℝ) + 1) (Set.right_mem_Icc.mpr (le_add_of_nonneg_right zero_le_one))
  simpa [r, Nat.cast_add, add_sub_cancel_left] using hstep

/-- The endpoint norm and discrete variation of a bounded profile after Mellin modulation. -/
theorem roughMellin_profile_variation_le
    (h : ℕ → ℂ) (t : ℝ) {L H : ℕ} (hL : 1 ≤ L) (hLH : L < H)
    (hH : H ≤ 2 * (L + 1)) (hh : ∀ n ∈ Finset.Ioc L H, ‖h n‖ ≤ 1) :
    let w : ℕ → ℂ := fun n => h n * (n : ℂ) ^ (Complex.I * (t : ℂ))
    ‖w H‖ + (∑ n ∈ Finset.Ioc L (H - 1), ‖w (n + 1) - w n‖) ≤
      1 + (∑ n ∈ Finset.Ioc L (H - 1), ‖h (n + 1) - h n‖) + |t| := by
  let phase : ℕ → ℂ := fun n => (n : ℂ) ^ (Complex.I * (t : ℂ))
  dsimp only
  change ‖h H * phase H‖ + (∑ n ∈ Finset.Ioc L (H - 1),
      ‖h (n + 1) * phase (n + 1) - h n * phase n‖) ≤ _
  have hphase (n : ℕ) (hn : 0 < n) : ‖phase n‖ = 1 := by
    simpa only [phase, Complex.ofReal_natCast] using
      mellinPhase_norm_eq_one t (n : ℝ) (Nat.cast_pos.mpr hn)
  have hLast : ‖h H * phase H‖ ≤ 1 := by
    rw [norm_mul, hphase H (by omega), mul_one]
    exact hh H (Finset.mem_Ioc.mpr ⟨hLH, le_rfl⟩)
  have hSteps : ∀ n ∈ Finset.Ioc L (H - 1),
      ‖h (n + 1) * phase (n + 1) - h n * phase n‖ ≤
        ‖h (n + 1) - h n‖ + |t| / ((L + 1 : ℕ) : ℝ) := by
    intro n hn
    have hn' := Finset.mem_Ioc.mp hn
    have hns : ‖phase (n + 1) - phase n‖ ≤ |t| / ((L + 1 : ℕ) : ℝ) :=
      mellinPhase_step_norm_le t (Nat.succ_pos L) (by omega)
    rw [show h (n + 1) * phase (n + 1) - h n * phase n =
      (h (n + 1) - h n) * phase (n + 1) + h n * (phase (n + 1) - phase n) by ring]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, hphase (n + 1) (Nat.succ_pos n), mul_one]
    refine add_le_add le_rfl ?_
    calc
      _ ≤ 1 * ‖phase (n + 1) - phase n‖ :=
        mul_le_mul_of_nonneg_right (hh n (Finset.mem_Ioc.mpr ⟨hn'.1, by omega⟩)) (norm_nonneg _)
      _ ≤ _ := by simpa only [one_mul] using hns
  have hLength : ((Finset.Ioc L (H - 1)).card : ℝ) ≤ ((L + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show (Finset.Ioc L (H - 1)).card ≤ L + 1 by rw [Nat.card_Ioc]; omega)
  have hPos : (0 : ℝ) < ((L + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos L)
  have hTotal : (∑ _n ∈ Finset.Ioc L (H - 1), |t| / ((L + 1 : ℕ) : ℝ)) ≤ |t| := by
    rw [Finset.sum_const, nsmul_eq_mul, ← mul_div_assoc]
    exact (div_le_iff₀ hPos).mpr (by
      rw [mul_comm |t|]
      exact mul_le_mul_of_nonneg_right hLength (abs_nonneg t))
  refine (add_le_add hLast (Finset.sum_le_sum hSteps)).trans ?_
  rw [Finset.sum_add_distrib, ← add_assoc]
  exact add_le_add le_rfl hTotal

end ImbalancedChen.Part3
