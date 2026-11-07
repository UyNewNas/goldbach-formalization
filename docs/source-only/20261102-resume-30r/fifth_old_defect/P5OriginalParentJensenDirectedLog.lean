import ImbalancedChen.P5OriginalSharpDirectedLog
import ImbalancedChen.P2DirectedLogRounding

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The parent Jensen producer uses the ONE-term upper logarithm with its
1/3 tail.  The later subdivision producer uses a DIFFERENT 1/9 tail.
This source licenses the original parent expression without replacing it
by the larger child expression.  No saved-old-field or integral licence
is a premise or conclusion of this scalar theorem.
-/
namespace ImbalancedChen.P5OriginalParentJensenDirectedLog
open scoped BigOperators
open P5OldFifthPointwiseQ P5OriginalSharpDirectedLog
open ImbalancedChen.Certificates.P2DirectedLogRounding

def parentUpperQ (y : ℚ) : ℚ :=
  2 * (y + y ^ 3 / (3 * (1 - y ^ 2)))

def parentLowerQ (z : ℚ) : ℚ := 2 * (z + z ^ 3 / 3 + z ^ 5 / 5)

def parentDirectedQ (b e : ℚ) : ℚ :=
  let a := b - e
  let z := e / (2 * (b - 1) - e)
  let y := (a - 2) / a
  (a * parentLowerQ z - e * parentUpperQ y) / (a * b)

noncomputable section

def parentUpper (y : ℝ) : ℝ :=
  2 * (y + y ^ 3 / (3 * (1 - y ^ 2)))

/-- Exact difference between the TWO producer tails, with its sign visible. -/
theorem parentUpper_sub_upper4 (y : ℝ) (hy : 1 - y ^ 2 ≠ 0) :
    parentUpper y - upper4 y =
      4 * (y ^ 5 / 15 + y ^ 7 / 35 + y ^ 9 / 63) / (1 - y ^ 2) := by
  unfold parentUpper upper4
  field_simp [hy]
  <;> ring

theorem log_le_parentUpper (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y < 1) :
    Real.log ((1 + y) / (1 - y)) ≤ parentUpper y := by
  have hd : 0 < 1 - y ^ 2 := by
    nlinarith [mul_pos (show 0 < 1 - y by linarith)
      (show 0 < 1 + y by linarith)]
  have htail : upper4 y ≤ parentUpper y := by
    apply le_of_sub_nonneg
    rw [parentUpper_sub_upper4 y hd.ne']
    positivity
  exact (log_le_upper4 y hy0 hy1).trans htail

/-- The old parent's actual directed subtraction.  The upper logarithm
is multiplied by minus e; using a lower logarithm there would be unsound. -/
theorem parentDirectedQ_le_Q (b e : ℚ)
    (hb : 2 < b) (he0 : 0 ≤ e) (he : e ≤ b - 2) :
    (parentDirectedQ b e : ℝ) ≤ Q (b : ℝ) (e : ℝ) := by
  let a : ℝ := (b : ℝ) - (e : ℝ)
  let z : ℝ := (e : ℝ) / (2 * ((b : ℝ) - 1) - (e : ℝ))
  let y : ℝ := (a - 2) / a
  have hbR : (2 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have heR : (0 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he0
  have hae : (e : ℝ) ≤ (b : ℝ) - 2 := by exact_mod_cast he
  have ha : 2 ≤ a := by dsimp [a]; linarith
  have ha0 : 0 < a := by linarith
  have hb0 : (0 : ℝ) < (b : ℝ) := by linarith
  have hy0 : 0 ≤ y := div_nonneg (by linarith) ha0.le
  have hy1 : y < 1 := (div_lt_one ha0).mpr (by linarith)
  have hd : 0 < 1 - y ^ 2 := by
    nlinarith [mul_pos (show 0 < 1 - y by linarith)
      (show 0 < 1 + y by linarith)]
  have htail : upper4 y ≤ parentUpper y := by
    apply le_of_sub_nonneg
    rw [parentUpper_sub_upper4 y hd.ne']
    positivity
  have hnum : a * lower3 z - (e : ℝ) * parentUpper y ≤
      a * lower3 z - (e : ℝ) * upper4 y :=
    sub_le_sub_left (mul_le_mul_of_nonneg_left htail heR) _
  have hdir := directed_Q_lower (b : ℝ) (e : ℝ) hbR heR hae
  have hcast : (parentDirectedQ b e : ℝ) =
      (a * lower3 z - (e : ℝ) * parentUpper y) / (a * (b : ℝ)) := by
    simp [parentDirectedQ, parentLowerQ, parentUpperQ, parentUpper,
      lower3, a, z, y]
  rw [hcast]
  exact (div_le_div_of_nonneg_right hnum (mul_pos ha0 hb0).le).trans hdir

/-- The literal ln/ld in adaptive.exact_term, hence also the rescaled
Jensen exact_term.  This is not the later subdivision 315-polynomial. -/
theorem parentUpper_expanded (Y C : ℝ) (hC : C ≠ 0)
    (hCY : C ^ 2 - Y ^ 2 ≠ 0) :
    parentUpper (Y / C) =
      2 * Y * (3 * C ^ 2 - 2 * Y ^ 2) /
        (3 * C * (C ^ 2 - Y ^ 2)) := by
  unfold parentUpper
  field_simp [hC, hCY]
  <;> ring

/-- Directed rounding is applied to the signed original expression.
No positivity of the rational minorant itself is silently assumed. -/
theorem original_parent_scalar_floor_sound (p b e : ℚ)
    (hp : 0 ≤ p) (hb : 2 < b) (he0 : 0 ≤ e) (he : e ≤ b - 2) :
    (roundDown 80 (p * parentDirectedQ b e) : ℝ) ≤
      (p : ℝ) * Q (b : ℝ) (e : ℝ) := by
  have hround : (roundDown 80 (p * parentDirectedQ b e) : ℝ) ≤
      (p : ℝ) * (parentDirectedQ b e : ℝ) := by
    exact_mod_cast roundDown_le 80 (p * parentDirectedQ b e)
  have hpR : (0 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  exact hround.trans
    (mul_le_mul_of_nonneg_left (parentDirectedQ_le_Q b e hb he0 he) hpR)

end
end ImbalancedChen.P5OriginalParentJensenDirectedLog
