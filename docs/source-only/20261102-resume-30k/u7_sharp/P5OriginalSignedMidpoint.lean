import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Signed midpoint error with the exact 1/24 constant used by the original
sharp-switch producer. This module has no U7 dependency. The remainder is
an equality of genuine integrals, proved by two explicit FTC primitives.
Both half-cell weights are nonnegative. Thus lower and upper second
derivative enclosures propagate without an absolute-value replacement.
-/

namespace ImbalancedChen.P5OriginalSignedMidpoint

noncomputable section
open Set MeasureTheory

def midpointError (f'' : ℝ → ℝ) (l r : ℝ) : ℝ :=
  (∫ x in l..((l + r) / 2), (x - l) ^ 2 / 2 * f'' x) +
    ∫ x in ((l + r) / 2)..r, (x - r) ^ 2 / 2 * f'' x

theorem half_weight_nonneg (v x : ℝ) : 0 ≤ (x - v) ^ 2 / 2 := by positivity

private theorem anchored_remainder {f f' f'' : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hf : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Icc a b, HasDerivAt f' (f'' x) x)
    (hc : ContinuousOn f'' (Icc a b)) (v : ℝ) :
    (∫ x in a..b, f x) =
      ((b - v) * f b - (b - v) ^ 2 / 2 * f' b) -
      ((a - v) * f a - (a - v) ^ 2 / 2 * f' a) +
        ∫ x in a..b, (x - v) ^ 2 / 2 * f'' x := by
  have hfc : ContinuousOn f (Icc a b) :=
    fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hw : ContinuousOn (fun x : ℝ => (x - v) ^ 2 / 2 * f'' x) (Icc a b) :=
    (((continuousOn_id.sub continuousOn_const).pow 2).div_const 2).mul hc
  have hi := hfc.intervalIntegrable_of_Icc hab
  have hwi := hw.intervalIntegrable_of_Icc hab
  have hd : ∀ x ∈ uIcc a b,
      HasDerivAt (fun y => (y - v) * f y - (y - v) ^ 2 / 2 * f' y)
        (f x - (x - v) ^ 2 / 2 * f'' x) x := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    have hlin := (hasDerivAt_id x).sub_const v
    apply ((hlin.mul (hf x hx)).sub
      (((hlin.pow 2).div_const 2).mul (hf' x hx))).congr_deriv
    ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hi.sub hwi)
  rw [intervalIntegral.integral_sub hi hwi] at hFTC
  linarith only [hFTC]

/-- Exact signed midpoint identity. No derivative bound is assumed. -/
theorem midpoint_identity {f f' f'' : ℝ → ℝ} {l r : ℝ} (hlr : l ≤ r)
    (hf : ∀ x ∈ Icc l r, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Icc l r, HasDerivAt f' (f'' x) x)
    (hc : ContinuousOn f'' (Icc l r)) :
    (∫ x in l..r, f x) = (r - l) * f ((l + r) / 2) + midpointError f'' l r := by
  let m := (l + r) / 2
  have hlm : l ≤ m := by dsimp [m]; linarith
  have hmr : m ≤ r := by dsimp [m]; linarith
  have hleft : Icc l m ⊆ Icc l r := fun x hx => ⟨hx.1, hx.2.trans hmr⟩
  have hright : Icc m r ⊆ Icc l r := fun x hx => ⟨hlm.trans hx.1, hx.2⟩
  have hfc : ContinuousOn f (Icc l r) :=
    fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hL := anchored_remainder hlm (fun x hx => hf x (hleft hx))
    (fun x hx => hf' x (hleft hx)) (hc.mono hleft) l
  have hR := anchored_remainder hmr (fun x hx => hf x (hright hx))
    (fun x hx => hf' x (hright hx)) (hc.mono hright) r
  rw [← intervalIntegral.integral_add_adjacent_intervals
    ((hfc.mono hleft).intervalIntegrable_of_Icc hlm)
    ((hfc.mono hright).intervalIntegrable_of_Icc hmr), hL, hR]
  dsimp only [midpointError, m]
  ring

private theorem half_weight_integral (a b v : ℝ) :
    (∫ x in a..b, (x - v) ^ 2 / 2) = ((b - v) ^ 3 - (a - v) ^ 3) / 6 := by
  have hd : ∀ x ∈ uIcc a b,
      HasDerivAt (fun y : ℝ => (y - v) ^ 3 / 6) ((x - v) ^ 2 / 2) x := by
    intro x hx
    apply ((((hasDerivAt_id x).sub_const v).pow 3).div_const 6).congr_deriv
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((((continuous_id.sub continuous_const).pow 2).div_const 2).intervalIntegrable a b)]
  ring

/-- The combined two half-cell masses are exactly delta cubed over 24. -/
theorem midpointError_const (q l r : ℝ) :
    midpointError (fun _ => q) l r = (r - l) ^ 3 / 24 * q := by
  unfold midpointError
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const,
    half_weight_integral, half_weight_integral]
  ring

/-- Positivity of the Peano kernel preserves signed second-derivative
order, including entirely negative intervals. -/
theorem midpointError_mono {g h : ℝ → ℝ} {l r : ℝ} (hlr : l ≤ r)
    (hg : ContinuousOn g (Icc l r)) (hh : ContinuousOn h (Icc l r))
    (hgh : ∀ x ∈ Icc l r, g x ≤ h x) : midpointError g l r ≤ midpointError h l r := by
  let m := (l + r) / 2
  have hlm : l ≤ m := by dsimp [m]; linarith
  have hmr : m ≤ r := by dsimp [m]; linarith
  have hleft : Icc l m ⊆ Icc l r := fun x hx => ⟨hx.1, hx.2.trans hmr⟩
  have hright : Icc m r ⊆ Icc l r := fun x hx => ⟨hlm.trans hx.1, hx.2⟩
  have hw (v : ℝ) : Continuous (fun x : ℝ => (x - v) ^ 2 / 2) :=
    ((continuous_id.sub continuous_const).pow 2).div_const 2
  have hL := intervalIntegral.integral_mono_on hlm
    (((hw l).continuousOn.mul (hg.mono hleft)).intervalIntegrable_of_Icc hlm)
    (((hw l).continuousOn.mul (hh.mono hleft)).intervalIntegrable_of_Icc hlm)
    (fun x hx => mul_le_mul_of_nonneg_left (hgh x (hleft hx)) (half_weight_nonneg l x))
  have hR := intervalIntegral.integral_mono_on hmr
    (((hw r).continuousOn.mul (hg.mono hright)).intervalIntegrable_of_Icc hmr)
    (((hw r).continuousOn.mul (hh.mono hright)).intervalIntegrable_of_Icc hmr)
    (fun x hx => mul_le_mul_of_nonneg_left (hgh x (hright hx)) (half_weight_nonneg r x))
  exact add_le_add hL hR

/-- Signed midpoint bounds with the producer's exact 1/24 factor. The
only enclosure premise is local, for the genuine second derivative. -/
theorem midpoint_bounds {f f' f'' : ℝ → ℝ} {l r L U : ℝ} (hlr : l ≤ r)
    (hf : ∀ x ∈ Icc l r, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Icc l r, HasDerivAt f' (f'' x) x)
    (hc : ContinuousOn f'' (Icc l r))
    (hbound : ∀ x ∈ Icc l r, L ≤ f'' x ∧ f'' x ≤ U) :
    (r - l) * (f ((l + r) / 2) + L * (r - l) ^ 2 / 24) ≤
        (∫ x in l..r, f x) ∧
      (∫ x in l..r, f x) ≤
        (r - l) * (f ((l + r) / 2) + U * (r - l) ^ 2 / 24) := by
  have hL := midpointError_mono hlr continuousOn_const hc (fun x hx => (hbound x hx).1)
  have hU := midpointError_mono hlr hc continuousOn_const (fun x hx => (hbound x hx).2)
  rw [midpointError_const] at hL hU
  rw [midpoint_identity hlr hf hf' hc]
  constructor <;> nlinarith only [hL, hU]

end
end ImbalancedChen.P5OriginalSignedMidpoint
