import ImbalancedChen.Part3CharacterMiddleZeroFirstPairs
import ImbalancedChen.Part3PrimitiveEisensteinFourierParameterAnalytic
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The actual nonzero-first primitive lattice rows, divided by height^s,
tend to zero at every fixed real s>1. Domination is the genuine convergent
height-one Eisenstein lattice seed, not an assumed cusp estimate.
The conclusion permits any fixed horizontal coordinate and any height
path tending to infinity with height at least one. -/

noncomputable section
open Complex UpperHalfPlane EisensteinSeries Filter Topology Set
open scoped UpperHalfPlane BigOperators
open ImbalancedChen.Part3.RealEisensteinSeedConvergence
open ImbalancedChen.Part3.PrimitiveEisensteinParameterAnalytic
open ImbalancedChen.Part3.PrimitiveEisensteinFourierParameterAnalytic

namespace ImbalancedChen.Part3.CharacterEisensteinGrowingHeight20261026b

/-- Numerator-free ORIGINAL lattice denominator at a real parameter. -/
def rowKernel (s : ℝ) (z : ℍ) (v : PrimitivePair) : ℝ :=
  ‖(v.1 0 : ℂ)*(z : ℂ)+(v.1 1 : ℂ)‖ ^ (-(2*s))

/-- A total height path; for y≥1 this is literally x+i*y. -/
def cuspPoint (x y : ℝ) : ℍ :=
  horizontalPoint (max 1 y) (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) x

@[simp] theorem cuspPoint_re (x y : ℝ) : (cuspPoint x y).re = x := rfl
@[simp] theorem cuspPoint_im (x y : ℝ) : (cuspPoint x y).im = max 1 y := rfl

theorem cuspPoint_im_tendsto (x : ℝ) :
    Tendsto (fun y : ℝ => (cuspPoint x y).im) atTop atTop :=
  tendsto_atTop_mono (fun y => le_max_right 1 y) tendsto_id

theorem linear_norm_pos (z : ℍ) (v : PrimitivePair) :
    0 < ‖(v.1 0 : ℂ)*(z : ℂ)+(v.1 1 : ℂ)‖ := by
  apply lt_of_le_of_ne (norm_nonneg _)
  intro h
  have hp := positiveBase_pos z v
  simp [positiveBase, ← h] at hp

theorem linear_norm_sq (z : ℍ) (v : PrimitivePair) :
    ‖(v.1 0 : ℂ)*(z : ℂ)+(v.1 1 : ℂ)‖^2 =
      ((v.1 0 : ℝ)*z.re+(v.1 1 : ℝ))^2 + ((v.1 0 : ℝ)*z.im)^2 := by
  simp [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, pow_two]

/-- The lower first-coordinate bound is paid by integrality, including
negative first coordinates; no natAbs character evaluation occurs. -/
theorem height_le_linear_norm (z : ℍ) (v : PrimitivePair) (hv : v.1 0 ≠ 0) :
    z.im ≤ ‖(v.1 0 : ℂ)*(z : ℂ)+(v.1 1 : ℂ)‖ := by
  have hcZ : 1 ≤ (v.1 0)^2 := by
    have hc : v.1 0 ≤ -1 ∨ 1 ≤ v.1 0 := by omega
    rcases hc with hc | hc <;> nlinarith
  have hcR : (1 : ℝ) ≤ (v.1 0 : ℝ)^2 := by exact_mod_cast hcZ
  have hm : z.im^2 ≤ ((v.1 0 : ℝ)*z.im)^2 := by
    calc
      z.im^2 = 1*z.im^2 := (one_mul _).symm
      _ ≤ (v.1 0 : ℝ)^2*z.im^2 :=
        mul_le_mul_of_nonneg_right hcR (sq_nonneg _)
      _ = ((v.1 0 : ℝ)*z.im)^2 := by ring
  have hsq : z.im^2 ≤ ‖(v.1 0 : ℂ)*(z : ℂ)+(v.1 1 : ℂ)‖^2 := by
    rw [linear_norm_sq]
    exact hm.trans (le_add_of_nonneg_left (sq_nonneg _))
  nlinarith [norm_nonneg ((v.1 0 : ℂ)*(z : ℂ)+(v.1 1 : ℂ))]

/-- For fixed horizontal coordinate, raising height from one increases
every literal lattice denominator. -/
theorem height_one_norm_le (x : ℝ) (z : ℍ) (hx : z.re = x)
    (hy : 1 ≤ z.im) (v : PrimitivePair) :
    ‖(v.1 0 : ℂ)*(horizontalPoint 1 zero_lt_one x : ℍ)+(v.1 1 : ℂ)‖ ≤
      ‖(v.1 0 : ℂ)*(z : ℂ)+(v.1 1 : ℂ)‖ := by
  have hm : (v.1 0 : ℝ)^2 ≤ ((v.1 0 : ℝ)*z.im)^2 := by
    have hh : (1 : ℝ) ≤ z.im^2 := by nlinarith
    calc
      (v.1 0 : ℝ)^2 = (v.1 0 : ℝ)^2*1 := (mul_one _).symm
      _ ≤ (v.1 0 : ℝ)^2*z.im^2 :=
        mul_le_mul_of_nonneg_left hh (sq_nonneg _)
      _ = ((v.1 0 : ℝ)*z.im)^2 := by ring
  have hsq :
      ‖(v.1 0 : ℂ)*(horizontalPoint 1 zero_lt_one x : ℍ)+(v.1 1 : ℂ)‖^2 ≤
        ‖(v.1 0 : ℂ)*(z : ℂ)+(v.1 1 : ℂ)‖^2 := by
    rw [linear_norm_sq, linear_norm_sq]
    simpa only [horizontalPoint, hx, mul_one] using
      add_le_add_left hm (((v.1 0 : ℝ)*x+(v.1 1 : ℝ))^2)
  nlinarith [norm_nonneg ((v.1 0 : ℂ)*(z : ℂ)+(v.1 1 : ℂ)),
    norm_nonneg ((v.1 0 : ℂ)*(horizontalPoint 1 zero_lt_one x : ℍ)+(v.1 1 : ℂ))]

theorem rowKernel_nonneg (s : ℝ) (z : ℍ) (v : PrimitivePair) :
    0 ≤ rowKernel s z v := Real.rpow_nonneg (norm_nonneg _) _

theorem rowKernel_height_one_le (s : ℝ) (hs : 1 < s) (x : ℝ)
    (z : ℍ) (hx : z.re = x) (hy : 1 ≤ z.im) (v : PrimitivePair) :
    rowKernel s z v ≤ seed s (horizontalPoint 1 zero_lt_one x) v.1 := by
  have h := Real.rpow_le_rpow_of_nonpos
    (linear_norm_pos (horizontalPoint 1 zero_lt_one x) v)
    (height_one_norm_le x z hx hy v) (by linarith : -(2*s) ≤ 0)
  simpa [rowKernel, seed, horizontalPoint] using h

theorem rowKernel_summable (s : ℝ) (hs : 1 < s) (z : ℍ) :
    Summable (rowKernel s z) := by
  have hp : z.im^s ≠ 0 := (Real.rpow_pos_of_pos z.im_pos s).ne'
  convert (primitiveSeed_summable s hs z).div_const (z.im^s) using 1
  funext v
  simp [seed, rowKernel, hp]

/-- This is a genuine termwise decay, obtained from the nonzero integer
first coordinate and the negative real power of the increasing height. -/
theorem rowKernel_tendsto_zero (s : ℝ) (hs : 1 < s)
    (z : ℝ → ℍ) (hz : Tendsto (fun y => (z y).im) atTop atTop)
    (v : PrimitivePair) (hv : v.1 0 ≠ 0) :
    Tendsto (fun y => rowKernel s (z y) v) atTop (nhds 0) := by
  have hden : Tendsto
      (fun y => ‖(v.1 0 : ℂ)*(z y : ℂ)+(v.1 1 : ℂ)‖) atTop atTop :=
    tendsto_atTop_mono (fun y => height_le_linear_norm (z y) v hv) hz
  exact (Real.tendsto_rpow_neg_atTop (by linarith : 0 < 2*s)).comp hden

/-- The exact normalized remainder after deleting the two zero-first
primitive rows; its signed complex weights remain present. -/
def weightedRemainder (w : PrimitivePair → ℂ) (s : ℝ) (z : ℍ) : ℂ :=
  ∑' v : PrimitivePair, if v.1 0 = 0 then 0 else w v*(rowKernel s z v : ℂ)

theorem weightedRemainder_summable (w : PrimitivePair → ℂ)
    (hw : ∀ v, ‖w v‖ ≤ 1) (s : ℝ) (hs : 1 < s) (z : ℍ) :
    Summable (fun v : PrimitivePair =>
      if v.1 0 = 0 then (0 : ℂ) else w v*(rowKernel s z v : ℂ)) := by
  apply Summable.of_norm_bounded (rowKernel_summable s hs z)
  intro v
  split_ifs
  · simpa using rowKernel_nonneg s z v
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (rowKernel_nonneg s z v)]
    exact (mul_le_mul_of_nonneg_right (hw v) (rowKernel_nonneg s z v)).trans_eq (one_mul _)

/-- Countable dominated convergence is supplied by the ACTUAL positive
height-one primitive Eisenstein lattice majorant. No remainder estimate is
assumed, and no non-absolutely-convergent reindexing is performed. -/
theorem weightedRemainder_tendsto_zero (w : PrimitivePair → ℂ)
    (hw : ∀ v, ‖w v‖ ≤ 1) (s : ℝ) (hs : 1 < s) (x : ℝ)
    (z : ℝ → ℍ) (hx : ∀ y, (z y).re = x) (hy : ∀ y, 1 ≤ (z y).im)
    (hz : Tendsto (fun y => (z y).im) atTop atTop) :
    Tendsto (fun y => weightedRemainder w s (z y)) atTop (nhds 0) := by
  let f : ℝ → PrimitivePair → ℂ := fun y v =>
    if v.1 0 = 0 then 0 else w v*(rowKernel s (z y) v : ℂ)
  have hpoint : ∀ v, Tendsto (fun y => f y v) atTop (nhds 0) := by
    intro v
    by_cases hv : v.1 0 = 0
    · simp only [f, hv, if_true]
      exact tendsto_const_nhds
    · simp only [f, hv, if_false]
      simpa using (Complex.continuous_ofReal.tendsto 0 |>.comp
        (rowKernel_tendsto_zero s hs z hz v hv)).const_mul (w v)
  have hbound : ∀ᶠ y : ℝ in atTop, ∀ v,
      ‖f y v‖ ≤ seed s (horizontalPoint 1 zero_lt_one x) v.1 := by
    exact Eventually.of_forall (fun y v => by
      dsimp only [f]
      split_ifs
      · simpa using (show 0 ≤ seed s (horizontalPoint 1 zero_lt_one x) v.1 by
          unfold seed; positivity)
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (rowKernel_nonneg s (z y) v)]
        exact ((mul_le_mul_of_nonneg_right (hw v)
          (rowKernel_nonneg s (z y) v)).trans_eq (one_mul _)).trans
          (rowKernel_height_one_le s hs x (z y) (hx y) (hy y) v))
  simpa only [weightedRemainder, f, tsum_zero] using
    tendsto_tsum_of_dominated_convergence
      (primitiveSeed_summable s hs (horizontalPoint 1 zero_lt_one x)) hpoint hbound

end ImbalancedChen.Part3.CharacterEisensteinGrowingHeight20261026b

