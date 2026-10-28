import ImbalancedChen.P5OldFifthPointwiseQ
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED_ZERO_CREDIT.
The ORIGINAL three-term lower log and four-term upper log with the sharp
1/9 geometric tail. This does not substitute Mathlib's coarser unweighted
tail. The lower bound reuses Mathlib's actual logarithmic sum inequality;
the upper bound follows from a nonnegative derivative of the exact finite
rational expression minus the actual logarithm.
-/
namespace ImbalancedChen.P5OriginalSharpDirectedLog
noncomputable section
open Set
open scoped BigOperators
open P5OldFifthPointwiseQ

def lower3 (x : ℝ) : ℝ := 2 * (x + x ^ 3 / 3 + x ^ 5 / 5)
def upper4 (x : ℝ) : ℝ :=
  2 * (x + x ^ 3 / 3 + x ^ 5 / 5 + x ^ 7 / 7 + x ^ 9 / (9 * (1 - x ^ 2)))

theorem lower3_le_log (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    lower3 x ≤ Real.log ((1 + x) / (1 - x)) := by
  have h := Real.sum_range_le_log_div hx0 hx1 3
  norm_num [Finset.sum_range_succ] at h
  unfold lower3
  nlinarith

private theorem sharp_gap_hasDerivAt (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y < 1) :
    HasDerivAt
      (fun x : ℝ => upper4 x - (Real.log (1 + x) - Real.log (1 - x)))
      ((4 / 9 : ℝ) * y ^ 10 / (1 - y ^ 2) ^ 2) y := by
  have hsq : 0 < 1 - y ^ 2 := by
    have hp := mul_pos (show 0 < 1 - y by linarith) (show 0 < 1 + y by linarith)
    nlinarith
  have hp : 1 + y ≠ 0 := by linarith
  have hm : 1 - y ≠ 0 := by linarith
  have hd : 9 * (1 - y ^ 2) ≠ 0 := mul_ne_zero (by norm_num) hsq.ne'
  have hbase := (((hasDerivAt_id y).add ((hasDerivAt_pow 3 y).div_const 3)).add
    ((hasDerivAt_pow 5 y).div_const 5)).add ((hasDerivAt_pow 7 y).div_const 7)
  have hden := ((hasDerivAt_const y (1 : ℝ)).sub (hasDerivAt_pow 2 y)).const_mul 9
  have htail := (hasDerivAt_pow 9 y).div hden hd
  have hu := (hbase.add htail).const_mul 2
  have hplus := ((hasDerivAt_const y (1 : ℝ)).add (hasDerivAt_id y)).log hp
  have hminus := ((hasDerivAt_const y (1 : ℝ)).sub (hasDerivAt_id y)).log hm
  have hlog := hplus.sub hminus
  convert hu.sub hlog using 1 <;> simp only [upper4]
  <;> field_simp [hsq.ne', hp, hm, hd]
  <;> ring

/-- Exact original sharp upper tail, including x=0. -/
theorem log_le_upper4 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Real.log ((1 + x) / (1 - x)) ≤ upper4 x := by
  let F : ℝ → ℝ := fun y => upper4 y - (Real.log (1 + y) - Real.log (1 - y))
  have hmono : MonotoneOn F (Icc 0 x) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 x)
    · intro y hy
      exact (sharp_gap_hasDerivAt y hy.1 (hy.2.trans_lt hx1)).continuousAt.continuousWithinAt
    · intro y hy
      have hi : y ∈ Icc 0 x := interior_subset hy
      exact (sharp_gap_hasDerivAt y hi.1 (hi.2.trans_lt hx1)).hasDerivWithinAt
    · intro y hy
      positivity
  have h := hmono ⟨le_rfl, hx0⟩ ⟨hx0, le_rfl⟩ hx0
  have hzero : F 0 = 0 := by simp [F, upper4]
  rw [hzero] at h
  change 0 ≤ upper4 x - (Real.log (1 + x) - Real.log (1 - x)) at h
  rw [Real.log_div (by linarith : 1 + x ≠ 0) (by linarith : 1 - x ≠ 0)]
  linarith

/-- Both required coefficient signs are retained in the directed Q bound. -/
theorem directed_Q_lower (b e : ℝ) (hb : 2 < b) (he0 : 0 ≤ e) (he : e ≤ b - 2) :
    let a := b - e
    let z := e / (2 * (b - 1) - e)
    let y := (a - 2) / a
    (a * lower3 z - e * upper4 y) / (a * b) ≤ Q b e := by
  dsimp only
  let a := b - e
  let z := e / (2 * (b - 1) - e)
  let y := (a - 2) / a
  have ha : 2 ≤ a := by dsimp [a]; linarith
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have ham1 : 0 < a - 1 := by linarith
  have hbm1 : 0 < b - 1 := by linarith
  have hzden : 0 < 2 * (b - 1) - e := by dsimp [a] at ha; linarith
  have hz0 : 0 ≤ z := div_nonneg he0 hzden.le
  have hz1 : z < 1 := by
    apply (div_lt_one hzden).mpr
    dsimp [a] at ha
    linarith
  have hy0 : 0 ≤ y := div_nonneg (by linarith) ha0.le
  have hy1 : y < 1 := by exact (div_lt_one ha0).mpr (by linarith)
  have hzx : (1 + z) / (1 - z) = (b - 1) / (a - 1) := by
    have h1z : 1 - z ≠ 0 := by linarith
    dsimp [z, a] at *
    field_simp [hzden.ne', ham1.ne', h1z]
    <;> ring
  have hyx : (1 + y) / (1 - y) = a - 1 := by
    have h1y : 1 - y ≠ 0 := by linarith
    dsimp [y]
    field_simp [ha0.ne', h1y]
    <;> ring
  have hL := lower3_le_log z hz0 hz1
  have hU := log_le_upper4 y hy0 hy1
  rw [hzx] at hL
  rw [hyx] at hU
  have hnum : a * lower3 z - e * upper4 y ≤
      a * Real.log ((b - 1) / (a - 1)) - e * Real.log (a - 1) :=
    sub_le_sub (mul_le_mul_of_nonneg_left hL ha0.le)
      (mul_le_mul_of_nonneg_left hU he0)
  have hid : Q b e =
      (a * Real.log ((b - 1) / (a - 1)) - e * Real.log (a - 1)) / (a * b) := by
    rw [Real.log_div hbm1.ne' ham1.ne']
    unfold Q firstF
    dsimp [a]
    field_simp [ha0.ne', hb0.ne']
    <;> ring
  rw [hid]
  exact div_le_div_of_nonneg_right hnum (mul_pos ha0 hb0).le

/-- Original producer's expanded numerator/denominator for L3. -/
theorem lower3_expanded (Z D : ℝ) (hD : D ≠ 0) :
    lower3 (Z / D) =
      2 * Z * (15 * D ^ 4 + 5 * Z ^ 2 * D ^ 2 + 3 * Z ^ 4) / (15 * D ^ 5) := by
  unfold lower3
  field_simp [hD]
  <;> ring

/-- Original producer's four-term sharp upper numerator, with its
necessary nonzero denominator guards exposed. -/
theorem upper4_expanded (Y C : ℝ) (hC : C ≠ 0) (hCY : C ^ 2 - Y ^ 2 ≠ 0) :
    upper4 (Y / C) =
      2 * Y * (315 * C ^ 8 - 210 * Y ^ 2 * C ^ 6 -
        42 * Y ^ 4 * C ^ 4 - 18 * Y ^ 6 * C ^ 2 - 10 * Y ^ 8) /
        (315 * C ^ 7 * (C ^ 2 - Y ^ 2)) := by
  unfold upper4
  field_simp [hC, hCY]
  <;> ring

end
end ImbalancedChen.P5OriginalSharpDirectedLog
