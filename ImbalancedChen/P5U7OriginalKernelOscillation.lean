import ImbalancedChen.P5U7OriginalBuchstabLipschitz

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
Explicit oscillation bound for the actual K=1 original U7 kernel on its
complete closed triangle. The proof uses the actual cross-seam Buchstab
Lipschitz theorem, exact rational-function differences, and the original
positive cutoff d=59/250>1/5. No kernel regularity estimate is assumed.
-/

namespace ImbalancedChen

noncomputable section

open LiLiuPrereqBuchstab

private theorem p5U7_inverse_abs_le_five {x : ℝ} (hx : (1 / 5 : ℝ) ≤ x) :
    |1 / x| ≤ 5 := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  rw [abs_of_pos (one_div_pos.mpr hx0)]
  apply (div_le_iff₀ hx0).mpr
  linarith only [hx]

private theorem p5U7_inverse_difference_le {x y : ℝ}
    (hx : (1 / 5 : ℝ) ≤ x) (hy : (1 / 5 : ℝ) ≤ y) :
    |1 / x - 1 / y| ≤ 25 * |x - y| := by
  have h := p5U7_abs_reciprocal_sub_le (a := 1 / 5) (by norm_num) hx hy
  have heq : |x - y| / (1 / 5 : ℝ) ^ 2 = 25 * |x - y| := by ring
  simpa only [heq] using h

private theorem p5U7_abs_triple_mul_le {x y z A B C : ℝ}
    (hx : |x| ≤ A) (hy : |y| ≤ B) (hz : |z| ≤ C) :
    |x * y * z| ≤ A * B * C := by
  have hA : 0 ≤ A := (abs_nonneg x).trans hx
  have hB : 0 ≤ B := (abs_nonneg y).trans hy
  rw [abs_mul, abs_mul]
  exact mul_le_mul (mul_le_mul hx hy (abs_nonneg y) hA) hz
    (abs_nonneg z) (mul_nonneg hA hB)

/-- Argument distortion on the actual original triangle. The conservative
coefficients 5 and 25 come from the true positive u cutoff. -/
theorem p5U7OmegaArgument_abs_sub_le {t u v w : ℝ}
    (h : p5U7OmegaClosedSupport t u) (h' : p5U7OmegaClosedSupport v w) :
    |p5U7OmegaArgument t u - p5U7OmegaArgument v w| ≤
      5 * |t - v| + 25 * |u - w| := by
  have hg := p5U7Omega_closed_geometry h
  have hg' := p5U7Omega_closed_geometry h'
  have hu : (1 / 5 : ℝ) ≤ u := by linarith only [h.1, h.2.1]
  have hw : (1 / 5 : ℝ) ≤ w := by linarith only [h'.1, h'.2.1]
  have hres : |1 - v| ≤ 1 := by
    rw [abs_of_nonneg (show 0 ≤ 1 - v by linarith only [hg'.2.2.2.1])]
    linarith only [h'.1]
  have heq : p5U7OmegaArgument t u - p5U7OmegaArgument v w =
      (v - t) * (1 / u) + (1 - v) * (1 / u - 1 / w) := by
    unfold p5U7OmegaArgument
    field_simp [hg.2.1.ne', hg'.2.1.ne']
    <;> ring
  have hfirst : |(v - t) * (1 / u)| ≤ 5 * |t - v| := by
    rw [abs_mul, abs_sub_comm v t]
    have hh := mul_le_mul_of_nonneg_left (p5U7_inverse_abs_le_five hu) (abs_nonneg (t - v))
    nlinarith only [hh]
  have hsecond : |(1 - v) * (1 / u - 1 / w)| ≤ 25 * |u - w| := by
    rw [abs_mul]
    have hh := mul_le_mul hres (p5U7_inverse_difference_le hu hw)
      (abs_nonneg (1 / u - 1 / w)) zero_le_one
    simpa only [one_mul] using hh
  rw [heq]
  exact (abs_add _ _).trans (add_le_add hfirst hsecond)

private def p5U7ReciprocalKernel (t u : ℝ) : ℝ := (1 / t) * (1 / u) * (1 / u)

private theorem p5U7ReciprocalKernel_abs_le {t u : ℝ}
    (ht : (1 / 5 : ℝ) ≤ t) (hu : (1 / 5 : ℝ) ≤ u) :
    |p5U7ReciprocalKernel t u| ≤ 125 := by
  have h := p5U7_abs_triple_mul_le (p5U7_inverse_abs_le_five ht)
    (p5U7_inverse_abs_le_five hu) (p5U7_inverse_abs_le_five hu)
  norm_num only [show (5 : ℝ) * 5 * 5 = 125 by norm_num] at h
  exact h

private theorem p5U7ReciprocalKernel_abs_sub_le {t u v w : ℝ}
    (ht : (1 / 5 : ℝ) ≤ t) (hu : (1 / 5 : ℝ) ≤ u)
    (hv : (1 / 5 : ℝ) ≤ v) (hw : (1 / 5 : ℝ) ≤ w) :
    |p5U7ReciprocalKernel t u - p5U7ReciprocalKernel v w| ≤
      625 * |t - v| + 1250 * |u - w| := by
  have heq : p5U7ReciprocalKernel t u - p5U7ReciprocalKernel v w =
      (1 / t - 1 / v) * (1 / u) * (1 / u) +
      (1 / v) * (1 / u - 1 / w) * (1 / u) +
      (1 / v) * (1 / w) * (1 / u - 1 / w) := by
    unfold p5U7ReciprocalKernel
    ring
  have h1 : |(1 / t - 1 / v) * (1 / u) * (1 / u)| ≤ 625 * |t - v| := by
    calc
      _ ≤ (25 * |t - v|) * 5 * 5 := p5U7_abs_triple_mul_le
        (p5U7_inverse_difference_le ht hv) (p5U7_inverse_abs_le_five hu)
        (p5U7_inverse_abs_le_five hu)
      _ = _ := by ring
  have h2 : |(1 / v) * (1 / u - 1 / w) * (1 / u)| ≤ 625 * |u - w| := by
    calc
      _ ≤ 5 * (25 * |u - w|) * 5 := p5U7_abs_triple_mul_le
        (p5U7_inverse_abs_le_five hv) (p5U7_inverse_difference_le hu hw)
        (p5U7_inverse_abs_le_five hu)
      _ = _ := by ring
  have h3 : |(1 / v) * (1 / w) * (1 / u - 1 / w)| ≤ 625 * |u - w| := by
    calc
      _ ≤ 5 * 5 * (25 * |u - w|) := p5U7_abs_triple_mul_le
        (p5U7_inverse_abs_le_five hv) (p5U7_inverse_abs_le_five hw)
        (p5U7_inverse_difference_le hu hw)
      _ = _ := by ring
  rw [heq]
  have htri := (abs_add
    ((1 / t - 1 / v) * (1 / u) * (1 / u) + (1 / v) * (1 / u - 1 / w) * (1 / u))
    ((1 / v) * (1 / w) * (1 / u - 1 / w))).trans
      (add_le_add_right (abs_add _ _) _)
  linarith only [htri, h1, h2, h3]

/-- Explicit actual-kernel oscillation, crossing the s=2 seam whenever
the two original points lie on opposite sides. No oscillation premise is
left to a rational mesh certificate. -/
theorem p5U7OmegaKernel_abs_sub_le_original {t u v w : ℝ}
    (h : p5U7OmegaClosedSupport t u) (h' : p5U7OmegaClosedSupport v w) :
    |p5U7OmegaKernel 1 t u - p5U7OmegaKernel 1 v w| ≤
      5000 * (|t - v| + |u - w|) := by
  have hg := p5U7Omega_closed_geometry h
  have hg' := p5U7Omega_closed_geometry h'
  have ht : (1 / 5 : ℝ) ≤ t := by linarith only [h.1]
  have hu : (1 / 5 : ℝ) ≤ u := by linarith only [h.1, h.2.1]
  have hv : (1 / 5 : ℝ) ≤ v := by linarith only [h'.1]
  have hw : (1 / 5 : ℝ) ≤ w := by linarith only [h'.1, h'.2.1]
  have harg := p5U7OmegaArgument_abs_sub_le h h'
  have hbuch := (p5U7_buchstab_abs_sub_le
    ⟨hg.2.2.2.2.1, hg.2.2.2.2.2⟩ ⟨hg'.2.2.2.2.1, hg'.2.2.2.2.2⟩).trans harg
  have hb' : |buchstab (p5U7OmegaArgument v w)| ≤ 1 := by
    rw [abs_of_nonneg (buchstab_nonneg hg'.2.2.2.2.1)]
    exact buchstab_le_one hg'.2.2.2.2.1
  have hR := p5U7ReciprocalKernel_abs_le ht hu
  have hRdiff := p5U7ReciprocalKernel_abs_sub_le ht hu hv hw
  have heq (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
      p5U7OmegaKernel 1 a b =
        buchstab (p5U7OmegaArgument a b) * p5U7ReciprocalKernel a b := by
    unfold p5U7OmegaKernel p5U7ReciprocalKernel
    field_simp [ha.ne', hb.ne']
    <;> ring
  rw [heq t u hg.1 hg.2.1, heq v w hg'.1 hg'.2.1]
  have hsplit :
      buchstab (p5U7OmegaArgument t u) * p5U7ReciprocalKernel t u -
        buchstab (p5U7OmegaArgument v w) * p5U7ReciprocalKernel v w =
      (buchstab (p5U7OmegaArgument t u) - buchstab (p5U7OmegaArgument v w)) *
        p5U7ReciprocalKernel t u +
      buchstab (p5U7OmegaArgument v w) *
        (p5U7ReciprocalKernel t u - p5U7ReciprocalKernel v w) := by ring
  rw [hsplit]
  have hfirst :
      |(buchstab (p5U7OmegaArgument t u) - buchstab (p5U7OmegaArgument v w)) *
        p5U7ReciprocalKernel t u| ≤ (5 * |t - v| + 25 * |u - w|) * 125 := by
    rw [abs_mul]
    exact mul_le_mul hbuch hR (abs_nonneg _) (by positivity)
  have hsecond :
      |buchstab (p5U7OmegaArgument v w) *
        (p5U7ReciprocalKernel t u - p5U7ReciprocalKernel v w)| ≤
      625 * |t - v| + 1250 * |u - w| := by
    rw [abs_mul]
    have hh := mul_le_mul hb' hRdiff (abs_nonneg _) zero_le_one
    simpa only [one_mul] using hh
  have htri := abs_add
    ((buchstab (p5U7OmegaArgument t u) - buchstab (p5U7OmegaArgument v w)) *
      p5U7ReciprocalKernel t u)
    (buchstab (p5U7OmegaArgument v w) *
      (p5U7ReciprocalKernel t u - p5U7ReciprocalKernel v w))
  nlinarith only [htri, hfirst, hsecond, abs_nonneg (t - v), abs_nonneg (u - w)]

end

end ImbalancedChen
