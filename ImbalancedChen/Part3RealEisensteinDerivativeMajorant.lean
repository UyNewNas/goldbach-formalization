import ImbalancedChen.Part3RealEisensteinSeedLaplacian
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.UniformConvergence
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Tactic

/-!
SOURCE ONLY, 2026-10-24. UNCOMPILED; no acceptance credit.

These are the concrete denominator inequalities behind local uniform first
and second derivative majorants for the real Eisenstein lattice summand.
They show that differentiation costs at most a factor of `1/y` or `1/y²`,
independent of `(c,d)`. On `y ≥ B > 0`, the already-proved summable seed
majorant therefore still has exponent `2s > 2`.
-/

namespace ImbalancedChen.Part3.RealEisensteinDerivativeMajorant

noncomputable section

open ImbalancedChen.Part3.RealEisensteinSeedLaplacian
open ImbalancedChen.Part3.RealEisensteinSeedConvergence
open Complex UpperHalfPlane EisensteinSeries
open scoped UpperHalfPlane

theorem Qx_abs_mul_y_le_Q (c d x y : ℝ) (hy : 0 < y) :
    |Qx c d x| * y ≤ Q c d x y := by
  have hcross : |2 * (c * y) * (c * x + d)| ≤
      (c * y) ^ 2 + (c * x + d) ^ 2 := by
    apply abs_le.mpr
    constructor <;>
      nlinarith [sq_nonneg ((c * y) + (c * x + d)),
        sq_nonneg ((c * y) - (c * x + d))]
  calc
    |Qx c d x| * y = |Qx c d x * y| := by rw [abs_mul, abs_of_pos hy]
    _ = |2 * (c * y) * (c * x + d)| := by congr 1; simp [Qx]; ring
    _ ≤ Q c d x y := by simpa [Q, add_comm] using hcross

theorem Qy_mul_y_le_two_Q (c d x y : ℝ) :
    Qy c y * y ≤ 2 * Q c d x y := by
  dsimp [Qy, Q]
  nlinarith [sq_nonneg (c * x + d)]

theorem c_sq_mul_y_sq_le_Q (c d x y : ℝ) :
    c ^ 2 * y ^ 2 ≤ Q c d x y := by
  dsimp [Q]
  nlinarith [sq_nonneg (c * x + d)]

private theorem firstX_factor (s c d x y : ℝ)
    (hq : 0 < Q c d x y) :
    firstX s c d x y =
      -s * coordinateSeed s c d x y * (Qx c d x / Q c d x y) := by
  unfold firstX coordinateSeed
  rw [Real.rpow_sub hq (-s) 1]
  simp only [Real.rpow_one]
  ring

private theorem firstY_factor (s c d x y : ℝ)
    (hy : 0 < y) (hq : 0 < Q c d x y) :
    firstY s c d x y =
      s * coordinateSeed s c d x y / y -
        s * coordinateSeed s c d x y * (Qy c y / Q c d x y) := by
  unfold firstY coordinateSeed
  rw [Real.rpow_sub hy s 1, Real.rpow_sub hq (-s) 1]
  simp only [Real.rpow_one]
  ring

private theorem secondX_factor (s c d x y : ℝ)
    (hq : 0 < Q c d x y) :
    secondX s c d x y =
      s * (s + 1) * coordinateSeed s c d x y *
        (Qx c d x / Q c d x y) ^ 2 -
      2 * s * coordinateSeed s c d x y * (c ^ 2 / Q c d x y) := by
  unfold secondX coordinateSeed
  rw [Real.rpow_sub hq (-s) 2, Real.rpow_sub hq (-s) 1]
  simp only [Real.rpow_natCast, Real.rpow_one]
  field_simp [hq.ne'] <;> ring

private theorem secondY_factor (s c d x y : ℝ)
    (hy : 0 < y) (hq : 0 < Q c d x y) :
    secondY s c d x y =
      s * (s - 1) * coordinateSeed s c d x y / y ^ 2 -
      2 * s ^ 2 * coordinateSeed s c d x y *
        (Qy c y / (y * Q c d x y)) +
      s * (s + 1) * coordinateSeed s c d x y *
        (Qy c y / Q c d x y) ^ 2 -
      2 * s * coordinateSeed s c d x y * (c ^ 2 / Q c d x y) := by
  unfold secondY coordinateSeed
  rw [Real.rpow_sub hy s 2, Real.rpow_sub hy s 1,
    Real.rpow_sub hq (-s) 2, Real.rpow_sub hq (-s) 1]
  simp only [Real.rpow_natCast, Real.rpow_one]
  field_simp [hy.ne', hq.ne'] <;> ring

theorem Qx_ratio_le (c d x y : ℝ) (hy : 0 < y)
    (hq : 0 < Q c d x y) :
    |Qx c d x| / Q c d x y ≤ 1 / y := by
  apply (div_le_div_iff₀ hq hy).2
  simpa using Qx_abs_mul_y_le_Q c d x y hy

theorem Qy_ratio_le (c d x y : ℝ) (hy : 0 < y)
    (hq : 0 < Q c d x y) :
    |Qy c y| / Q c d x y ≤ 2 / y := by
  have hqy : 0 ≤ Qy c y := by unfold Qy; positivity
  apply (div_le_div_iff₀ hq hy).2
  rw [abs_of_nonneg hqy]
  simpa using Qy_mul_y_le_two_Q c d x y

theorem c_sq_ratio_le (c d x y : ℝ) (hy : 0 < y)
    (hq : 0 < Q c d x y) :
    c ^ 2 / Q c d x y ≤ 1 / y ^ 2 := by
  apply (div_le_div_iff₀ hq (sq_pos_of_pos hy)).2
  simpa using c_sq_mul_y_sq_le_Q c d x y

theorem abs_firstX_le (s c d x y : ℝ) (hs : 1 < s)
    (hcd : c ≠ 0 ∨ d ≠ 0) (hy : 0 < y) :
    |firstX s c d x y| ≤ s * coordinateSeed s c d x y / y := by
  have hq := Q_pos hcd hy (x := x)
  have hf : 0 ≤ coordinateSeed s c d x y := by unfold coordinateSeed; positivity
  rw [firstX_factor s c d x y hq]
  have hr := Qx_ratio_le c d x y hy hq
  rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg (by linarith : 0 ≤ s),
    abs_of_nonneg hf, abs_div, abs_of_pos hq]
  calc
    s * coordinateSeed s c d x y * (|Qx c d x| / Q c d x y) ≤
        s * coordinateSeed s c d x y * (1 / y) :=
          mul_le_mul_of_nonneg_left hr (by positivity)
    _ = s * coordinateSeed s c d x y / y := by ring

theorem abs_firstY_le (s c d x y : ℝ) (hs : 1 < s)
    (hcd : c ≠ 0 ∨ d ≠ 0) (hy : 0 < y) :
    |firstY s c d x y| ≤ 3 * s * coordinateSeed s c d x y / y := by
  have hq := Q_pos hcd hy (x := x)
  have hf : 0 ≤ coordinateSeed s c d x y := by unfold coordinateSeed; positivity
  rw [firstY_factor s c d x y hy hq]
  have hr := Qy_ratio_le c d x y hy hq
  have hqy : 0 ≤ Qy c y := by unfold Qy; positivity
  have hbound : s * coordinateSeed s c d x y *
      (Qy c y / Q c d x y) ≤
      2 * s * coordinateSeed s c d x y / y := by
    calc
      _ ≤ s * coordinateSeed s c d x y * (2 / y) :=
        mul_le_mul_of_nonneg_left (by simpa [abs_of_nonneg hqy] using hr)
          (by positivity)
      _ = 2 * s * coordinateSeed s c d x y / y := by ring
  have hfirst : 0 ≤ s * coordinateSeed s c d x y / y := by positivity
  have hsecond : 0 ≤ s * coordinateSeed s c d x y *
      (Qy c y / Q c d x y) := by positivity
  calc
    |s * coordinateSeed s c d x y / y -
        s * coordinateSeed s c d x y * (Qy c y / Q c d x y)| ≤
      s * coordinateSeed s c d x y / y +
        s * coordinateSeed s c d x y * (Qy c y / Q c d x y) := by
          simpa [abs_of_nonneg hfirst, abs_of_nonneg hsecond] using
            abs_sub_le (s * coordinateSeed s c d x y / y)
              (s * coordinateSeed s c d x y * (Qy c y / Q c d x y))
    _ ≤ 3 * s * coordinateSeed s c d x y / y := by nlinarith

theorem abs_secondX_le (s c d x y : ℝ) (hs : 1 < s)
    (hcd : c ≠ 0 ∨ d ≠ 0) (hy : 0 < y) :
    |secondX s c d x y| ≤
      s * (s + 3) * coordinateSeed s c d x y / y ^ 2 := by
  have hq := Q_pos hcd hy (x := x)
  have hf : 0 ≤ coordinateSeed s c d x y := by unfold coordinateSeed; positivity
  have hr : |Qx c d x / Q c d x y| ≤ 1 / y := by
    simpa [abs_div, abs_of_pos hq] using Qx_ratio_le c d x y hy hq
  have hr2 : (Qx c d x / Q c d x y) ^ 2 ≤ 1 / y ^ 2 := by
    calc
      _ = |Qx c d x / Q c d x y| ^ 2 := by rw [sq_abs]
      _ ≤ (1 / y) ^ 2 := by gcongr
      _ = 1 / y ^ 2 := by ring
  have hc := c_sq_ratio_le c d x y hy hq
  rw [secondX_factor s c d x y hq]
  let a := s * (s + 1) * coordinateSeed s c d x y *
    (Qx c d x / Q c d x y) ^ 2
  let b := 2 * s * coordinateSeed s c d x y * (c ^ 2 / Q c d x y)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hboundA : a ≤ s * (s + 1) * coordinateSeed s c d x y / y ^ 2 := by
    dsimp [a]
    calc
      _ ≤ s * (s + 1) * coordinateSeed s c d x y * (1 / y ^ 2) :=
        mul_le_mul_of_nonneg_left hr2 (by positivity)
      _ = _ := by ring
  have hboundB : b ≤ 2 * s * coordinateSeed s c d x y / y ^ 2 := by
    dsimp [b]
    calc
      _ ≤ 2 * s * coordinateSeed s c d x y * (1 / y ^ 2) :=
        mul_le_mul_of_nonneg_left hc (by positivity)
      _ = _ := by ring
  have habs : |a - b| ≤ a + b := by
    simpa [abs_of_nonneg ha, abs_of_nonneg hb] using abs_sub_le a b
  dsimp [a, b] at habs hboundA hboundB ⊢
  nlinarith

theorem abs_secondY_le (s c d x y : ℝ) (hs : 1 < s)
    (hcd : c ≠ 0 ∨ d ≠ 0) (hy : 0 < y) :
    |secondY s c d x y| ≤
      (9 * s ^ 2 + 5 * s) * coordinateSeed s c d x y / y ^ 2 := by
  have hq := Q_pos hcd hy (x := x)
  have hf : 0 ≤ coordinateSeed s c d x y := by unfold coordinateSeed; positivity
  have hqy : 0 ≤ Qy c y := by unfold Qy; positivity
  have hr : Qy c y / Q c d x y ≤ 2 / y := by
    simpa [abs_of_nonneg hqy] using Qy_ratio_le c d x y hy hq
  have hr1 : Qy c y / (y * Q c d x y) ≤ 2 / y ^ 2 := by
    apply (div_le_div_iff₀ (mul_pos hy hq) (sq_pos_of_pos hy)).2
    have hbase := Qy_mul_y_le_two_Q c d x y
    have hmul := mul_le_mul_of_nonneg_left hbase hy.le
    nlinarith
  have hr2 : (Qy c y / Q c d x y) ^ 2 ≤ 4 / y ^ 2 := by
    calc
      _ ≤ (2 / y) ^ 2 := by gcongr
      _ = 4 / y ^ 2 := by ring
  have hc := c_sq_ratio_le c d x y hy hq
  rw [secondY_factor s c d x y hy hq]
  let a := s * (s - 1) * coordinateSeed s c d x y / y ^ 2
  let b := 2 * s ^ 2 * coordinateSeed s c d x y *
    (Qy c y / (y * Q c d x y))
  let e := s * (s + 1) * coordinateSeed s c d x y *
    (Qy c y / Q c d x y) ^ 2
  let f := 2 * s * coordinateSeed s c d x y * (c ^ 2 / Q c d x y)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hf' : 0 ≤ f := by dsimp [f]; positivity
  have hbb : b ≤ 4 * s ^ 2 * coordinateSeed s c d x y / y ^ 2 := by
    dsimp [b]
    calc
      _ ≤ 2 * s ^ 2 * coordinateSeed s c d x y * (2 / y ^ 2) :=
        mul_le_mul_of_nonneg_left hr1 (by positivity)
      _ = _ := by ring
  have hee : e ≤ 4 * s * (s + 1) * coordinateSeed s c d x y / y ^ 2 := by
    dsimp [e]
    calc
      _ ≤ s * (s + 1) * coordinateSeed s c d x y * (4 / y ^ 2) :=
        mul_le_mul_of_nonneg_left hr2 (by positivity)
      _ = _ := by ring
  have hff : f ≤ 2 * s * coordinateSeed s c d x y / y ^ 2 := by
    dsimp [f]
    calc
      _ ≤ 2 * s * coordinateSeed s c d x y * (1 / y ^ 2) :=
        mul_le_mul_of_nonneg_left hc (by positivity)
      _ = _ := by ring
  have habs : |a - b + e - f| ≤ a + b + e + f := by
    rw [abs_le]
    constructor <;> nlinarith
  dsimp [a, b, e, f] at habs hbb hee hff ⊢
  nlinarith

/-- A real coordinate point in the actual upper half plane. -/
def point (x y : ℝ) (hy : 0 < y) : ℍ :=
  UpperHalfPlane.mk ((x : ℂ) + (y : ℂ) * Complex.I) (by simpa using hy)

@[simp] theorem point_re (x y : ℝ) (hy : 0 < y) :
    (point x y hy).re = x := by
  simp [point, Complex.add_re, Complex.mul_re]

@[simp] theorem point_im (x y : ℝ) (hy : 0 < y) :
    (point x y hy).im = y := by
  simp [point, Complex.add_im, Complex.mul_im]

private theorem primitive_nonzero (v : EisensteinSeries.gammaSet 1 1 0) :
    v.1 ≠ 0 := by
  intro hv
  have hg : (v.1 0).gcd (v.1 1) = 1 := v.2.2
  simp [hv] at hg

private theorem primitive_real_nonzero (v : EisensteinSeries.gammaSet 1 1 0) :
    (v.1 0 : ℝ) ≠ 0 ∨ (v.1 1 : ℝ) ≠ 0 := by
  by_contra h
  push_neg at h
  apply primitive_nonzero v
  ext i
  fin_cases i
  · exact_mod_cast h.1
  · exact_mod_cast h.2

/-- Absolute convergence of the actual coordinate seed over Mathlib's
primitive-pair index. -/
theorem primitive_coordinateSeed_summable (s : ℝ) (hs : 1 < s)
    (x y : ℝ) (hy : 0 < y) :
    Summable (fun v : EisensteinSeries.gammaSet 1 1 0 =>
      coordinateSeed s (v.1 0 : ℝ) (v.1 1 : ℝ) x y) := by
  have h := primitiveSeed_summable s hs (point x y hy)
  apply h.congr
  intro v
  simpa [point_re, point_im] using
    (coordinateSeed_eq_seed s (point x y hy) v.1).symm

private theorem primitive_normMajorant_summable (s : ℝ) (hs : 1 < s) :
    Summable (fun v : EisensteinSeries.gammaSet 1 1 0 =>
      ‖v.1‖ ^ (-(2 * s))) :=
  (EisensteinSeries.summable_one_div_norm_rpow
    (by linarith : (2 : ℝ) < 2 * s)).subtype _

/-- The single seed is dominated on a bounded-height vertical strip by the
same exponent-`2s` primitive lattice majorant as in the seed module. -/
theorem coordinateSeed_boundedStrip (s : ℝ) (hs : 1 < s)
    (A B Y x y : ℝ) (hB : 0 < B) (hx : |x| ≤ A)
    (hy : B ≤ y) (hY : y ≤ Y) (v : Fin 2 → ℤ) :
    coordinateSeed s (v 0 : ℝ) (v 1 : ℝ) x y ≤
      (Y ^ s * EisensteinSeries.r ⟨⟨A, B⟩, hB⟩ ^ (-(2 * s))) *
        ‖v‖ ^ (-(2 * s)) := by
  have hypos : 0 < y := hB.trans_le hy
  let z : ℍ := point x y hypos
  have hz : z ∈ verticalStrip A B := by
    simpa [z] using And.intro hx hy
  have hb := seed_bound_on_boundedStrip s hs A B Y hB v z hz (by simpa [z] using hY)
  simpa [z] using (le_trans (le_of_eq (coordinateSeed_eq_seed s z v)) hb)

/-- One majorant simultaneously controls the value and the first two
coordinate derivatives. The constants depend only on `s,B,Y,A`, never on
the primitive pair. -/
theorem coordinateDerivatives_boundedStrip (s : ℝ) (hs : 1 < s)
    (A B Y x y : ℝ) (hB : 0 < B) (hx : |x| ≤ A)
    (hy : B ≤ y) (hY : y ≤ Y) (v : EisensteinSeries.gammaSet 1 1 0) :
    let C := Y ^ s * EisensteinSeries.r ⟨⟨A, B⟩, hB⟩ ^ (-(2 * s))
    let M := ‖v.1‖ ^ (-(2 * s))
    |firstX s (v.1 0 : ℝ) (v.1 1 : ℝ) x y| ≤ (s / B * C) * M ∧
    |firstY s (v.1 0 : ℝ) (v.1 1 : ℝ) x y| ≤ (3 * s / B * C) * M ∧
    |secondX s (v.1 0 : ℝ) (v.1 1 : ℝ) x y| ≤
      (s * (s + 3) / B ^ 2 * C) * M ∧
    |secondY s (v.1 0 : ℝ) (v.1 1 : ℝ) x y| ≤
      ((9 * s ^ 2 + 5 * s) / B ^ 2 * C) * M := by
  dsimp
  have hypos : 0 < y := hB.trans_le hy
  have hcd := primitive_real_nonzero v
  have hseed := coordinateSeed_boundedStrip s hs A B Y x y hB hx hy hY v.1
  have hseed0 : 0 ≤ coordinateSeed s (v.1 0 : ℝ) (v.1 1 : ℝ) x y := by
    unfold coordinateSeed
    positivity
  have hC0 : 0 ≤ Y ^ s *
      EisensteinSeries.r ⟨⟨A, B⟩, hB⟩ ^ (-(2 * s)) := by positivity
  have hM0 : 0 ≤ ‖v.1‖ ^ (-(2 * s)) := by positivity
  constructor
  · calc
      _ ≤ s * coordinateSeed s (v.1 0 : ℝ) (v.1 1 : ℝ) x y / y :=
        abs_firstX_le s _ _ x y hs hcd hypos
      _ ≤ s * coordinateSeed s (v.1 0 : ℝ) (v.1 1 : ℝ) x y / B := by
        gcongr
      _ ≤ (s / B * (Y ^ s *
          EisensteinSeries.r ⟨⟨A, B⟩, hB⟩ ^ (-(2 * s)))) *
          ‖v.1‖ ^ (-(2 * s)) := by
        have h := mul_le_mul_of_nonneg_left hseed
          (show 0 ≤ s / B by positivity)
        nlinarith
  constructor
  · calc
      _ ≤ 3 * s * coordinateSeed s (v.1 0 : ℝ) (v.1 1 : ℝ) x y / y :=
        abs_firstY_le s _ _ x y hs hcd hypos
      _ ≤ 3 * s * coordinateSeed s (v.1 0 : ℝ) (v.1 1 : ℝ) x y / B := by
        gcongr
      _ ≤ (3 * s / B * (Y ^ s *
          EisensteinSeries.r ⟨⟨A, B⟩, hB⟩ ^ (-(2 * s)))) *
          ‖v.1‖ ^ (-(2 * s)) := by
        have h := mul_le_mul_of_nonneg_left hseed
          (show 0 ≤ 3 * s / B by positivity)
        nlinarith
  constructor
  · calc
      _ ≤ s * (s + 3) * coordinateSeed s (v.1 0 : ℝ) (v.1 1 : ℝ) x y / y ^ 2 :=
        abs_secondX_le s _ _ x y hs hcd hypos
      _ ≤ s * (s + 3) * coordinateSeed s (v.1 0 : ℝ) (v.1 1 : ℝ) x y / B ^ 2 := by
        gcongr
      _ ≤ (s * (s + 3) / B ^ 2 * (Y ^ s *
          EisensteinSeries.r ⟨⟨A, B⟩, hB⟩ ^ (-(2 * s)))) *
          ‖v.1‖ ^ (-(2 * s)) := by
        have h := mul_le_mul_of_nonneg_left hseed
          (show 0 ≤ s * (s + 3) / B ^ 2 by positivity)
        nlinarith
  · calc
      _ ≤ (9 * s ^ 2 + 5 * s) *
          coordinateSeed s (v.1 0 : ℝ) (v.1 1 : ℝ) x y / y ^ 2 :=
        abs_secondY_le s _ _ x y hs hcd hypos
      _ ≤ (9 * s ^ 2 + 5 * s) *
          coordinateSeed s (v.1 0 : ℝ) (v.1 1 : ℝ) x y / B ^ 2 := by
        gcongr
      _ ≤ ((9 * s ^ 2 + 5 * s) / B ^ 2 * (Y ^ s *
          EisensteinSeries.r ⟨⟨A, B⟩, hB⟩ ^ (-(2 * s)))) *
          ‖v.1‖ ^ (-(2 * s)) := by
        have h := mul_le_mul_of_nonneg_left hseed
          (show 0 ≤ (9 * s ^ 2 + 5 * s) / B ^ 2 by positivity)
        nlinarith

end

end ImbalancedChen.Part3.RealEisensteinDerivativeMajorant
