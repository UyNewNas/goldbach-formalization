import ImbalancedChen.P5OldFifthFirstFConcavity
import Mathlib.Analysis.Calculus.MeanValue

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The exact log_bounds(x,m=14) used by the original fifth Taylor pilot.
The upper remainder includes 1/29; the coarser existing logarithm
certificate remainder is not substituted.  Both signs in Gmid are kept.
-/
namespace ImbalancedChen.P5OriginalTaylorLogBounds
noncomputable section
open Set
open scoped BigOperators
open P5OldFifthPointwiseQ

def oddTerm (z : ℝ) (k : ℕ) : ℝ :=
  z ^ (2 * k + 1) / (2 * (k : ℝ) + 1)

def partial14 (z : ℝ) : ℝ := 2 * ∑ k ∈ Finset.range 14, oddTerm z k

def upper14 (z : ℝ) : ℝ := partial14 z + 2 * z ^ 29 / (29 * (1 - z ^ 2))

def logLower14 (x : ℝ) : ℝ := partial14 ((x - 1) / (x + 1))

def logUpper14 (x : ℝ) : ℝ := upper14 ((x - 1) / (x + 1))

theorem oddTerm_hasDerivAt (z : ℝ) (k : ℕ) :
    HasDerivAt (fun y => oddTerm y k) (z ^ (2 * k)) z := by
  have h := (hasDerivAt_pow (2 * k + 1) z).div_const (2 * (k : ℝ) + 1)
  convert h using 1 <;>
    simp only [oddTerm, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_one]
  <;> field_simp [show 2 * (k : ℝ) + 1 ≠ 0 by positivity]
  <;> ring

theorem partial14_hasDerivAt (z : ℝ) :
    HasDerivAt partial14 (2 * ∑ k ∈ Finset.range 14, z ^ (2 * k)) z := by
  exact (HasDerivAt.fun_sum (u := Finset.range 14)
    (fun k _ => oddTerm_hasDerivAt z k)).const_mul 2

/-- The actual sharp fourteen-term upper-tail remainder has a positive
derivative.  Its scale is 4/29, and its power is 30. -/
theorem upper14_log_gap_hasDerivAt (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z < 1) :
    HasDerivAt
      (fun y : ℝ => upper14 y - (Real.log (1 + y) - Real.log (1 - y)))
      ((4 / 29 : ℝ) * z ^ 30 / (1 - z ^ 2) ^ 2) z := by
  have hsq : 0 < 1 - z ^ 2 := by
    nlinarith [mul_pos (show 0 < 1 - z by linarith)
      (show 0 < 1 + z by linarith)]
  have hp : 1 + z ≠ 0 := by linarith
  have hm : 1 - z ≠ 0 := by linarith
  have hd : 29 * (1 - z ^ 2) ≠ 0 := mul_ne_zero (by norm_num) hsq.ne'
  have hden := ((hasDerivAt_const z (1 : ℝ)).sub (hasDerivAt_pow 2 z)).const_mul 29
  have htail := ((hasDerivAt_pow 29 z).const_mul 2).div hden hd
  have hu := (partial14_hasDerivAt z).add htail
  have hplus := ((hasDerivAt_const z (1 : ℝ)).add (hasDerivAt_id z)).log hp
  have hminus := ((hasDerivAt_const z (1 : ℝ)).sub (hasDerivAt_id z)).log hm
  convert hu.sub (hplus.sub hminus) using 1
  · rfl
  · norm_num [Finset.sum_range_succ]
    field_simp [hsq.ne', hp, hm, hd]
    <;> ring

theorem partial14_le_log_ratio (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z < 1) :
    partial14 z ≤ Real.log ((1 + z) / (1 - z)) := by
  simpa [partial14, oddTerm] using Real.sum_range_le_log_div hz0 hz1 14

theorem log_ratio_le_upper14 (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z < 1) :
    Real.log ((1 + z) / (1 - z)) ≤ upper14 z := by
  let F : ℝ → ℝ := fun y => upper14 y - (Real.log (1 + y) - Real.log (1 - y))
  have hmono : MonotoneOn F (Icc 0 z) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 z)
    · intro y hy
      exact (upper14_log_gap_hasDerivAt y hy.1
        (hy.2.trans_lt hz1)).continuousAt.continuousWithinAt
    · intro y hy
      have hi : y ∈ Icc 0 z := interior_subset hy
      exact (upper14_log_gap_hasDerivAt y hi.1
        (hi.2.trans_lt hz1)).hasDerivWithinAt
    · intro y _
      positivity
  have h := hmono ⟨le_rfl, hz0⟩ ⟨hz0, le_rfl⟩ hz0
  have hzero : F 0 = 0 := by
    norm_num [F, upper14, partial14, oddTerm, Finset.sum_range_succ]
  rw [hzero] at h
  change 0 ≤ upper14 z - (Real.log (1 + z) - Real.log (1 - z)) at h
  rw [Real.log_div (by linarith : 1 + z ≠ 0) (by linarith : 1 - z ≠ 0)]
  linarith

/-- Exactly the real semantics of pilot.log_bounds, including x=1. -/
theorem original_log14_bounds (x : ℝ) (hx : 1 ≤ x) :
    logLower14 x ≤ Real.log x ∧ Real.log x ≤ logUpper14 x := by
  let z := (x - 1) / (x + 1)
  have hd : 0 < x + 1 := by linarith
  have hz0 : 0 ≤ z := div_nonneg (by linarith) hd.le
  have hz1 : z < 1 := (div_lt_one hd).mpr (by linarith)
  have hid : (1 + z) / (1 - z) = x := by
    have h1z : 1 - z ≠ 0 := by linarith
    dsimp [z] at *
    field_simp [hd.ne', h1z]
    <;> ring
  have hl := partial14_le_log_ratio z hz0 hz1
  have hu := log_ratio_le_upper14 z hz0 hz1
  rw [hid] at hl hu
  exact ⟨hl, hu⟩

def midpointLower (weight sn so : ℝ) : ℝ :=
  weight * (logLower14 (sn - 1) / sn - logUpper14 (so - 1) / so)

/-- The positive new coefficient gets the lower log; the subtracted old
coefficient gets the upper log.  This is the original signed Gmid. -/
theorem original_midpoint_lower (weight sn so : ℝ)
    (hw : 0 ≤ weight) (hn : 2 ≤ sn) (ho : 2 ≤ so) :
    midpointLower weight sn so ≤ weight * (firstF sn - firstF so) := by
  have hn0 : 0 < sn := by linarith
  have ho0 : 0 < so := by linarith
  have hl := (original_log14_bounds (sn - 1) (by linarith)).1
  have hu := (original_log14_bounds (so - 1) (by linarith)).2
  exact mul_le_mul_of_nonneg_left
    (sub_le_sub (div_le_div_of_nonneg_right hl hn0.le)
      (div_le_div_of_nonneg_right hu ho0.le)) hw

end
end ImbalancedChen.P5OriginalTaylorLogBounds
