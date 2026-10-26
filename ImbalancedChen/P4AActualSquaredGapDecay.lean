import ImbalancedChen.ActualThirdOriginalLocalCurvature
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
SOURCE ONLY / UNCOMPILED.

Actual normalized gap decay from the already supplied derivatives of the
genuine upper/lower factors. No replacement F/f is defined. The delay
identity, continuity at the closed endpoint, and the derivative sign are
proved here; no decay, derivative-sign, or anchor enclosure is a premise.

The actual canonical unnormalized gap already has a source-DDE decay theorem
in ActualSieveGapTailDecay. This file supplies the direct upper/lower derivative
route and the exact normalized APIs needed by the original integer anchors.
-/

namespace ImbalancedChen.P4AActualSquaredGapDecay20261024zSourceOnly

noncomputable section

open Set
open OriginalU2CoupledRecurrenceSourceOnly

/-- These are precisely the existing canonical factors with the positive
amplitude normalization, on their entire common definition domain. -/
theorem normalized_gap_eq_actualSieveGap_div (s : ℝ) :
    upper s - lower s =
      actualSieveGap s / (2 * Real.exp Real.eulerMascheroniConstant) := by
  unfold upper lower thirdTailLowerFactor actualSieveGap A
  ring

theorem normalized_gap_nonneg {s : ℝ} (hs : 2 ≤ s) :
    0 ≤ upper s - lower s := by
  exact sub_nonneg.mpr (lower_le_upper hs)

/-- Subtracting an increasing lower factor from a decreasing upper factor
gives the actual gap order, including the closed endpoint two. -/
theorem antitoneOn_normalized_gap :
    AntitoneOn (fun s : ℝ => upper s - lower s) (Ici 2) := by
  intro x hx y hy hxy
  exact sub_le_sub (upper_antitone hx hy hxy) (lower_monotone hx hy hxy)

/-- Exact normalized delay equation from the actual factor derivatives. -/
theorem hasDerivAt_normalized_gap {s : ℝ} (hs : 3 < s) :
    HasDerivAt (fun t : ℝ => upper t - lower t)
      (-((upper (s - 1) - lower (s - 1)) + (upper s - lower s)) / s) s := by
  have hd := (hasDerivAt_upper_tail hs).sub
    (hasDerivAt_lower (by linarith : 2 < s))
  apply hd.congr_deriv
  dsimp only [upperSlope, lowerSlope]
  ring

/-- The factor continuity supplies the left endpoint independently of any
derivative assertion at the knot three. -/
theorem continuousOn_normalized_gap :
    ContinuousOn (fun s : ℝ => upper s - lower s) (Ici 3) := by
  intro s hs
  have hs2 : 2 < s := by change 3 ≤ s at hs; linarith
  exact ((continuousAt_upper hs2).sub (continuousAt_lower hs2)).continuousWithinAt

theorem continuousOn_square_mul_normalized_gap :
    ContinuousOn (fun s : ℝ => s ^ 2 * (upper s - lower s)) (Ici 3) := by
  exact (continuousOn_id.pow 2).mul continuousOn_normalized_gap

/-- Product differentiation cancels the current gap once, leaving the
nonpositive difference between the current and delayed genuine gaps. -/
theorem hasDerivAt_square_mul_normalized_gap {s : ℝ} (hs : 3 < s) :
    HasDerivAt (fun t : ℝ => t ^ 2 * (upper t - lower t))
      (s * ((upper s - lower s) - (upper (s - 1) - lower (s - 1)))) s := by
  have hs0 : s ≠ 0 := by linarith
  have hsquare : HasDerivAt (fun t : ℝ => t ^ 2) (s + s) s := by
    simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one, two_mul] using
      hasDerivAt_pow 2 s
  have hd := hsquare.mul (hasDerivAt_normalized_gap hs)
  apply hd.congr_deriv
  field_simp [hs0] <;> ring

theorem square_mul_normalized_gap_slope_nonpos {s : ℝ} (hs : 3 < s) :
    s * ((upper s - lower s) - (upper (s - 1) - lower (s - 1))) ≤ 0 := by
  have hgap := antitoneOn_normalized_gap
    (show s - 1 ∈ Ici (2 : ℝ) by change 2 ≤ s - 1; linarith)
    (show s ∈ Ici (2 : ℝ) by change 2 ≤ s; linarith)
    (by linarith : s - 1 ≤ s)
  exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (sub_nonpos.mpr hgap)

/-- Closed-domain squared gap decay for the existing actual normalized
factors. Continuity includes three; derivatives are used only above three. -/
theorem antitoneOn_square_mul_normalized_gap :
    AntitoneOn (fun s : ℝ => s ^ 2 * (upper s - lower s)) (Ici 3) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 3)
    continuousOn_square_mul_normalized_gap
    (f' := fun s => s *
      ((upper s - lower s) - (upper (s - 1) - lower (s - 1))))
  · intro s hs
    have hs3 : 3 < s := by simpa only [interior_Ici, mem_Ioi] using hs
    exact (hasDerivAt_square_mul_normalized_gap hs3).hasDerivWithinAt
  · intro s hs
    have hs3 : 3 < s := by simpa only [interior_Ici, mem_Ioi] using hs
    exact square_mul_normalized_gap_slope_nonpos hs3

/-- Any real anchor k>=3 gives the genuine normalized quadratic tail. -/
theorem normalized_gap_le_quadratic_tail {k s : ℝ}
    (hk : 3 ≤ k) (hks : k ≤ s) :
    upper s - lower s ≤ (upper k - lower k) * (k / s) ^ 2 := by
  have hbound := antitoneOn_square_mul_normalized_gap hk (hk.trans hks) hks
  have hspos : 0 < s := by linarith
  rw [div_pow, ← mul_div_assoc]
  apply (le_div_iff₀ (sq_pos_of_pos hspos)).2
  calc
    (upper s - lower s) * s ^ 2 = s ^ 2 * (upper s - lower s) := mul_comm _ _
    _ ≤ k ^ 2 * (upper k - lower k) := hbound
    _ = (upper k - lower k) * k ^ 2 := mul_comm _ _

/-- The literal anchor*k^2/s^2 shape needed by the original integer reader. -/
theorem normalized_gap_le_anchor_div_sq {k s : ℝ}
    (hk : 3 ≤ k) (hks : k ≤ s) :
    upper s - lower s ≤ (upper k - lower k) * k ^ 2 / s ^ 2 := by
  calc
    upper s - lower s ≤ (upper k - lower k) * (k / s) ^ 2 :=
      normalized_gap_le_quadratic_tail hk hks
    _ = (upper k - lower k) * k ^ 2 / s ^ 2 := by rw [div_pow]; ring

end

end ImbalancedChen.P4AActualSquaredGapDecay20261024zSourceOnly
